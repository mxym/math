-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0609 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0609 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0609 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0609_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142598777207040 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609Coded : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 1))]
theorem atom0609Coded_decode : atom0609 = SparsePolynomial.decodeCubic 24 atom0609Coded := by decide +kernel
theorem atom0609Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) := by
  have h := atom0609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0610 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0610 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0610 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0610_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121344224601600 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610Coded : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 1))]
theorem atom0610Coded_decode : atom0610 = SparsePolynomial.decodeCubic 24 atom0610Coded := by decide +kernel
theorem atom0610Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded) := by
  have h := atom0610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0611 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0611 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0611 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0611_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129213729335592 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611Coded : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 1))]
theorem atom0611Coded_decode : atom0611 = SparsePolynomial.decodeCubic 24 atom0611Coded := by decide +kernel
theorem atom0611Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) := by
  have h := atom0611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0612 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0612 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0612 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0612_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156989643019704 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612Coded : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 1))]
theorem atom0612Coded_decode : atom0612 = SparsePolynomial.decodeCubic 24 atom0612Coded := by decide +kernel
theorem atom0612Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) := by
  have h := atom0612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0613 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0613 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0613 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0613_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (178123796942256 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613Coded : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 1))]
theorem atom0613Coded_decode : atom0613 = SparsePolynomial.decodeCubic 24 atom0613Coded := by decide +kernel
theorem atom0613Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded) := by
  have h := atom0613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0614 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0614 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0614 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0614_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218964915186336 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614Coded : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 1))]
theorem atom0614Coded_decode : atom0614 = SparsePolynomial.decodeCubic 24 atom0614Coded := by decide +kernel
theorem atom0614Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) := by
  have h := atom0614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0615 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0615 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0615 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0615_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205962588216000 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615Coded : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 1))]
theorem atom0615Coded_decode : atom0615 = SparsePolynomial.decodeCubic 24 atom0615Coded := by decide +kernel
theorem atom0615Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded) := by
  have h := atom0615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0616 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0616 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0616 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0616_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187448867020800 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616Coded : CoefficientMerge.Poly := [(nat_lit 734, Int.ofNat (nat_lit 1))]
theorem atom0616Coded_decode : atom0616 = SparsePolynomial.decodeCubic 24 atom0616Coded := by decide +kernel
theorem atom0616Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) := by
  have h := atom0616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0617 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0617 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0617 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0617_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191115655718400 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617Coded : CoefficientMerge.Poly := [(nat_lit 735, Int.ofNat (nat_lit 1))]
theorem atom0617Coded_decode : atom0617 = SparsePolynomial.decodeCubic 24 atom0617Coded := by decide +kernel
theorem atom0617Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) := by
  have h := atom0617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0618 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0618 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0618 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0618_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177048679046400 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618Coded : CoefficientMerge.Poly := [(nat_lit 736, Int.ofNat (nat_lit 1))]
theorem atom0618Coded_decode : atom0618 = SparsePolynomial.decodeCubic 24 atom0618Coded := by decide +kernel
theorem atom0618Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded) := by
  have h := atom0618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0619 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0619 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0619 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0619_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177880810060800 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619Coded : CoefficientMerge.Poly := [(nat_lit 737, Int.ofNat (nat_lit 1))]
theorem atom0619Coded_decode : atom0619 = SparsePolynomial.decodeCubic 24 atom0619Coded := by decide +kernel
theorem atom0619Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) := by
  have h := atom0619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0620 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0620 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0620 = ((g 1) * (g 6) * (g 18)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0620_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (227305139846400 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620Coded : CoefficientMerge.Poly := [(nat_lit 738, Int.ofNat (nat_lit 1))]
theorem atom0620Coded_decode : atom0620 = SparsePolynomial.decodeCubic 24 atom0620Coded := by decide +kernel
theorem atom0620Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded) := by
  have h := atom0620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0621 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0621 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0621 = ((g 1) * (g 6) * (g 19)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0621_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197144498073600 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621Coded : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 1))]
theorem atom0621Coded_decode : atom0621 = SparsePolynomial.decodeCubic 24 atom0621Coded := by decide +kernel
theorem atom0621Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) := by
  have h := atom0621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0622 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0622 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0622 = ((g 1) * (g 6) * (g 20)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0622_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (243868509561600 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622Coded : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 1))]
theorem atom0622Coded_decode : atom0622 = SparsePolynomial.decodeCubic 24 atom0622Coded := by decide +kernel
theorem atom0622Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) := by
  have h := atom0622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0623 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0623 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0623 = ((g 1) * (g 6) * (g 21)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0623_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229597929792000 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623Coded : CoefficientMerge.Poly := [(nat_lit 741, Int.ofNat (nat_lit 1))]
theorem atom0623Coded_decode : atom0623 = SparsePolynomial.decodeCubic 24 atom0623Coded := by decide +kernel
theorem atom0623Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded) := by
  have h := atom0623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0624 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0624 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0624 = ((g 1) * (g 6) * (g 22)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0624_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292791670752000 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624Coded : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 1))]
theorem atom0624Coded_decode : atom0624 = SparsePolynomial.decodeCubic 24 atom0624Coded := by decide +kernel
theorem atom0624Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) := by
  have h := atom0624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0625 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0625 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0625 = ((g 1) * (g 6) * (g 23)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0625_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (280178158176000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625Coded : CoefficientMerge.Poly := [(nat_lit 743, Int.ofNat (nat_lit 1))]
theorem atom0625Coded_decode : atom0625 = SparsePolynomial.decodeCubic 24 atom0625Coded := by decide +kernel
theorem atom0625Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded) := by
  have h := atom0625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0626 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0626 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0626 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0626_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97409907302400 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626Coded : CoefficientMerge.Poly := [(nat_lit 751, Int.ofNat (nat_lit 1))]
theorem atom0626Coded_decode : atom0626 = SparsePolynomial.decodeCubic 24 atom0626Coded := by decide +kernel
theorem atom0626Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) := by
  have h := atom0626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0627 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0627 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0627 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0627_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166327558467840 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627Coded : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 1))]
theorem atom0627Coded_decode : atom0627 = SparsePolynomial.decodeCubic 24 atom0627Coded := by decide +kernel
theorem atom0627Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) := by
  have h := atom0627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0628 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0628 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0628 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0628_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145263690951720 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628Coded : CoefficientMerge.Poly := [(nat_lit 753, Int.ofNat (nat_lit 1))]
theorem atom0628Coded_decode : atom0628 = SparsePolynomial.decodeCubic 24 atom0628Coded := by decide +kernel
theorem atom0628Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded) := by
  have h := atom0628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0629 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0629 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0629 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0629_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170879862994104 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629Coded : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 1))]
theorem atom0629Coded_decode : atom0629 = SparsePolynomial.decodeCubic 24 atom0629Coded := by decide +kernel
theorem atom0629Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) := by
  have h := atom0629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0630 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0630 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0630 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0630_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193055872007856 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630Coded : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 1))]
theorem atom0630Coded_decode : atom0630 = SparsePolynomial.decodeCubic 24 atom0630Coded := by decide +kernel
theorem atom0630Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded) := by
  have h := atom0630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0631 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0631 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0631 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0631_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (234938845343136 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631Coded : CoefficientMerge.Poly := [(nat_lit 756, Int.ofNat (nat_lit 1))]
theorem atom0631Coded_decode : atom0631 = SparsePolynomial.decodeCubic 24 atom0631Coded := by decide +kernel
theorem atom0631Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) := by
  have h := atom0631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0632 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0632 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0632 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0632_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221947149547200 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632Coded : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 1))]
theorem atom0632Coded_decode : atom0632 = SparsePolynomial.decodeCubic 24 atom0632Coded := by decide +kernel
theorem atom0632Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) := by
  have h := atom0632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0633 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0633 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0633 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0633_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203444059526400 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633Coded : CoefficientMerge.Poly := [(nat_lit 758, Int.ofNat (nat_lit 1))]
theorem atom0633Coded_decode : atom0633 = SparsePolynomial.decodeCubic 24 atom0633Coded := by decide +kernel
theorem atom0633Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded) := by
  have h := atom0633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0634 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0634 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0634 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0634_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207121479398400 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634Coded : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 1))]
theorem atom0634Coded_decode : atom0634 = SparsePolynomial.decodeCubic 24 atom0634Coded := by decide +kernel
theorem atom0634Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) := by
  have h := atom0634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0635 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0635 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0635 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0635_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193065133900800 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635Coded : CoefficientMerge.Poly := [(nat_lit 760, Int.ofNat (nat_lit 1))]
theorem atom0635Coded_decode : atom0635 = SparsePolynomial.decodeCubic 24 atom0635Coded := by decide +kernel
theorem atom0635Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded) := by
  have h := atom0635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0636 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0636 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0636 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0636_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193907896089600 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636Coded : CoefficientMerge.Poly := [(nat_lit 761, Int.ofNat (nat_lit 1))]
theorem atom0636Coded_decode : atom0636 = SparsePolynomial.decodeCubic 24 atom0636Coded := by decide +kernel
theorem atom0636Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) := by
  have h := atom0636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0637 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0637 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0637 = ((g 1) * (g 7) * (g 18)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0637_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244507561267200 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637Coded : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 1))]
theorem atom0637Coded_decode : atom0637 = SparsePolynomial.decodeCubic 24 atom0637Coded := by decide +kernel
theorem atom0637Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) := by
  have h := atom0637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0638 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0638 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0638 = ((g 1) * (g 7) * (g 19)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0638_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216686959104000 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638Coded : CoefficientMerge.Poly := [(nat_lit 763, Int.ofNat (nat_lit 1))]
theorem atom0638Coded_decode : atom0638 = SparsePolynomial.decodeCubic 24 atom0638Coded := by decide +kernel
theorem atom0638Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded) := by
  have h := atom0638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0639 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0639 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0639 = ((g 1) * (g 7) * (g 20)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0639_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265751010201600 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639Coded : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 1))]
theorem atom0639Coded_decode : atom0639 = SparsePolynomial.decodeCubic 24 atom0639Coded := by decide +kernel
theorem atom0639Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) := by
  have h := atom0639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0640 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0640 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0640 = ((g 1) * (g 7) * (g 21)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0640_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256149878476800 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640Coded : CoefficientMerge.Poly := [(nat_lit 765, Int.ofNat (nat_lit 1))]
theorem atom0640Coded_decode : atom0640 = SparsePolynomial.decodeCubic 24 atom0640Coded := by decide +kernel
theorem atom0640Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded) := by
  have h := atom0640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0641 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0641 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0641 = ((g 1) * (g 7) * (g 22)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0641_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (326703148352000 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641Coded : CoefficientMerge.Poly := [(nat_lit 766, Int.ofNat (nat_lit 1))]
theorem atom0641Coded_decode : atom0641 = SparsePolynomial.decodeCubic 24 atom0641Coded := by decide +kernel
theorem atom0641Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) := by
  have h := atom0641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0642 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0642 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0642 = ((g 1) * (g 7) * (g 23)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0642_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316265679676800 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642Coded : CoefficientMerge.Poly := [(nat_lit 767, Int.ofNat (nat_lit 1))]
theorem atom0642Coded_decode : atom0642 = SparsePolynomial.decodeCubic 24 atom0642Coded := by decide +kernel
theorem atom0642Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) := by
  have h := atom0642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0643 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0643 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0643 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0643_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113923664870400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643Coded : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 1))]
theorem atom0643Coded_decode : atom0643 = SparsePolynomial.decodeCubic 24 atom0643Coded := by decide +kernel
theorem atom0643Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded) := by
  have h := atom0643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0644 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0644 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0644 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0644_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204854516840160 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644Coded : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 1))]
theorem atom0644Coded_decode : atom0644 = SparsePolynomial.decodeCubic 24 atom0644Coded := by decide +kernel
theorem atom0644Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) := by
  have h := atom0644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0645 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0645 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0645 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0645_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188840203618968 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645Coded : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 1))]
theorem atom0645Coded_decode : atom0645 = SparsePolynomial.decodeCubic 24 atom0645Coded := by decide +kernel
theorem atom0645Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded) := by
  have h := atom0645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0646 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0646 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0646 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0646_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207125640705456 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646Coded : CoefficientMerge.Poly := [(nat_lit 779, Int.ofNat (nat_lit 1))]
theorem atom0646Coded_decode : atom0646 = SparsePolynomial.decodeCubic 24 atom0646Coded := by decide +kernel
theorem atom0646Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) := by
  have h := atom0646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0647 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0647 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0647 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0647_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (246967428555936 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647Coded : CoefficientMerge.Poly := [(nat_lit 780, Int.ofNat (nat_lit 1))]
theorem atom0647Coded_decode : atom0647 = SparsePolynomial.decodeCubic 24 atom0647Coded := by decide +kernel
theorem atom0647Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) := by
  have h := atom0647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0648 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0648 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0648 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0648_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233476067563200 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648Coded : CoefficientMerge.Poly := [(nat_lit 781, Int.ofNat (nat_lit 1))]
theorem atom0648Coded_decode : atom0648 = SparsePolynomial.decodeCubic 24 atom0648Coded := by decide +kernel
theorem atom0648Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded) := by
  have h := atom0648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0649 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0649 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0649 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0649_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214473312345600 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649Coded : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 1))]
theorem atom0649Coded_decode : atom0649 = SparsePolynomial.decodeCubic 24 atom0649Coded := by decide +kernel
theorem atom0649Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) := by
  have h := atom0649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0650 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0650 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0650 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0650_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217651067020800 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650Coded : CoefficientMerge.Poly := [(nat_lit 783, Int.ofNat (nat_lit 1))]
theorem atom0650Coded_decode : atom0650 = SparsePolynomial.decodeCubic 24 atom0650Coded := by decide +kernel
theorem atom0650Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded) := by
  have h := atom0650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0651 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0651 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0651 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0651_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203095056326400 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651Coded : CoefficientMerge.Poly := [(nat_lit 784, Int.ofNat (nat_lit 1))]
theorem atom0651Coded_decode : atom0651 = SparsePolynomial.decodeCubic 24 atom0651Coded := by decide +kernel
theorem atom0651Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) := by
  have h := atom0651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0652 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0652 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0652 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0652_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203438153318400 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652Coded : CoefficientMerge.Poly := [(nat_lit 785, Int.ofNat (nat_lit 1))]
theorem atom0652Coded_decode : atom0652 = SparsePolynomial.decodeCubic 24 atom0652Coded := by decide +kernel
theorem atom0652Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) := by
  have h := atom0652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0653 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0653 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0653 = ((g 1) * (g 8) * (g 18)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0653_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (255265128518400 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653Coded : CoefficientMerge.Poly := [(nat_lit 786, Int.ofNat (nat_lit 1))]
theorem atom0653Coded_decode : atom0653 = SparsePolynomial.decodeCubic 24 atom0653Coded := by decide +kernel
theorem atom0653Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded) := by
  have h := atom0653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0654 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0654 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0654 = ((g 1) * (g 8) * (g 19)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0654_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230398811596800 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654Coded : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 1))]
theorem atom0654Coded_decode : atom0654 = SparsePolynomial.decodeCubic 24 atom0654Coded := by decide +kernel
theorem atom0654Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) := by
  have h := atom0654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0655 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0655 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0655 = ((g 1) * (g 8) * (g 20)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0655_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282417147936000 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655Coded : CoefficientMerge.Poly := [(nat_lit 788, Int.ofNat (nat_lit 1))]
theorem atom0655Coded_decode : atom0655 = SparsePolynomial.decodeCubic 24 atom0655Coded := by decide +kernel
theorem atom0655Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded) := by
  have h := atom0655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0656 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0656 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0656 = ((g 1) * (g 8) * (g 21)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0656_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279224251891200 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656Coded : CoefficientMerge.Poly := [(nat_lit 789, Int.ofNat (nat_lit 1))]
theorem atom0656Coded_decode : atom0656 = SparsePolynomial.decodeCubic 24 atom0656Coded := by decide +kernel
theorem atom0656Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) := by
  have h := atom0656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0657 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0657 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0657 = ((g 1) * (g 8) * (g 22)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0657_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (356557454803200 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657Coded : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 1))]
theorem atom0657Coded_decode : atom0657 = SparsePolynomial.decodeCubic 24 atom0657Coded := by decide +kernel
theorem atom0657Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) := by
  have h := atom0657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0658 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0658 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0658 = ((g 1) * (g 8) * (g 23)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0658_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349745019724800 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658Coded : CoefficientMerge.Poly := [(nat_lit 791, Int.ofNat (nat_lit 1))]
theorem atom0658Coded_decode : atom0658 = SparsePolynomial.decodeCubic 24 atom0658Coded := by decide +kernel
theorem atom0658Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded) := by
  have h := atom0658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0659 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0659 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0659 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0659_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136999274369760 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659Coded : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 1))]
theorem atom0659Coded_decode : atom0659 = SparsePolynomial.decodeCubic 24 atom0659Coded := by decide +kernel
theorem atom0659Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) := by
  have h := atom0659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0660 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0660 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0660 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0660_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (255486130384320 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660Coded : CoefficientMerge.Poly := [(nat_lit 802, Int.ofNat (nat_lit 1))]
theorem atom0660Coded_decode : atom0660 = SparsePolynomial.decodeCubic 24 atom0660Coded := by decide +kernel
theorem atom0660Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded) := by
  have h := atom0660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0661 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0661 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0661 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0661_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242659403316000 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661Coded : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 1))]
theorem atom0661Coded_decode : atom0661 = SparsePolynomial.decodeCubic 24 atom0661Coded := by decide +kernel
theorem atom0661Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) := by
  have h := atom0661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0662 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0662 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0662 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0662_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272104064602128 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662Coded : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 1))]
theorem atom0662Coded_decode : atom0662 = SparsePolynomial.decodeCubic 24 atom0662Coded := by decide +kernel
theorem atom0662Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) := by
  have h := atom0662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0663 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0663 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0663 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0663_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256061221753392 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663Coded : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 1))]
theorem atom0663Coded_decode : atom0663 = SparsePolynomial.decodeCubic 24 atom0663Coded := by decide +kernel
theorem atom0663Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded) := by
  have h := atom0663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0664 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0664 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0664 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0664_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236048504967792 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664Coded : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 1))]
theorem atom0664Coded_decode : atom0664 = SparsePolynomial.decodeCubic 24 atom0664Coded := by decide +kernel
theorem atom0664Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) := by
  have h := atom0664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0665 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0665 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0665 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0665_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238216298074992 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665Coded : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 1))]
theorem atom0665Coded_decode : atom0665 = SparsePolynomial.decodeCubic 24 atom0665Coded := by decide +kernel
theorem atom0665Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded) := by
  have h := atom0665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0666 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0666 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0666 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0666_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222650325812592 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666Coded : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 1))]
theorem atom0666Coded_decode : atom0666 = SparsePolynomial.decodeCubic 24 atom0666Coded := by decide +kernel
theorem atom0666Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) := by
  have h := atom0666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0667 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0667 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0667 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0667_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221983461236592 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667Coded : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 1))]
theorem atom0667Coded_decode : atom0667 = SparsePolynomial.decodeCubic 24 atom0667Coded := by decide +kernel
theorem atom0667Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) := by
  have h := atom0667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0668 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0668 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0668 = ((g 1) * (g 9) * (g 18)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0668_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273902208783984 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668Coded : CoefficientMerge.Poly := [(nat_lit 810, Int.ofNat (nat_lit 1))]
theorem atom0668Coded_decode : atom0668 = SparsePolynomial.decodeCubic 24 atom0668Coded := by decide +kernel
theorem atom0668Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded) := by
  have h := atom0668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0669 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0669 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0669 = ((g 1) * (g 9) * (g 19)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0669_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250229398125168 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669Coded : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 1))]
theorem atom0669Coded_decode : atom0669 = SparsePolynomial.decodeCubic 24 atom0669Coded := by decide +kernel
theorem atom0669Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) := by
  have h := atom0669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0670 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0670 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0670 = ((g 1) * (g 9) * (g 20)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0670_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (303441240727152 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670Coded : CoefficientMerge.Poly := [(nat_lit 812, Int.ofNat (nat_lit 1))]
theorem atom0670Coded_decode : atom0670 = SparsePolynomial.decodeCubic 24 atom0670Coded := by decide +kernel
theorem atom0670Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded) := by
  have h := atom0670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0671 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0671 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0671 = ((g 1) * (g 9) * (g 21)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0671_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (303645318775920 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671Coded : CoefficientMerge.Poly := [(nat_lit 813, Int.ofNat (nat_lit 1))]
theorem atom0671Coded_decode : atom0671 = SparsePolynomial.decodeCubic 24 atom0671Coded := by decide +kernel
theorem atom0671Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) := by
  have h := atom0671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0672 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0672 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0672 = ((g 1) * (g 9) * (g 22)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0672_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (368500279875840 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672Coded : CoefficientMerge.Poly := [(nat_lit 814, Int.ofNat (nat_lit 1))]
theorem atom0672Coded_decode : atom0672 = SparsePolynomial.decodeCubic 24 atom0672Coded := by decide +kernel
theorem atom0672Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) := by
  have h := atom0672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0673 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0673 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0673 = ((g 1) * (g 9) * (g 23)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0673_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (362803493738880 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673Coded : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 1))]
theorem atom0673Coded_decode : atom0673 = SparsePolynomial.decodeCubic 24 atom0673Coded := by decide +kernel
theorem atom0673Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded) := by
  have h := atom0673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0674 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0674 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0674 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0674_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164555278414560 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674Coded : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 1))]
theorem atom0674Coded_decode : atom0674 = SparsePolynomial.decodeCubic 24 atom0674Coded := by decide +kernel
theorem atom0674Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) := by
  have h := atom0674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0675 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0675 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0675 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0675_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316431248712480 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675Coded : CoefficientMerge.Poly := [(nat_lit 827, Int.ofNat (nat_lit 1))]
theorem atom0675Coded_decode : atom0675 = SparsePolynomial.decodeCubic 24 atom0675Coded := by decide +kernel
theorem atom0675Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded) := by
  have h := atom0675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0676 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0676 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0676 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0676_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (322461649501200 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676Coded : CoefficientMerge.Poly := [(nat_lit 828, Int.ofNat (nat_lit 1))]
theorem atom0676Coded_decode : atom0676 = SparsePolynomial.decodeCubic 24 atom0676Coded := by decide +kernel
theorem atom0676Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) := by
  have h := atom0676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0677 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0677 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0677 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0677_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (304203431906352 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677Coded : CoefficientMerge.Poly := [(nat_lit 829, Int.ofNat (nat_lit 1))]
theorem atom0677Coded_decode : atom0677 = SparsePolynomial.decodeCubic 24 atom0677Coded := by decide +kernel
theorem atom0677Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) := by
  have h := atom0677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0678 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0678 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0678 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0678_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282670457181552 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678Coded : CoefficientMerge.Poly := [(nat_lit 830, Int.ofNat (nat_lit 1))]
theorem atom0678Coded_decode : atom0678 = SparsePolynomial.decodeCubic 24 atom0678Coded := by decide +kernel
theorem atom0678Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded) := by
  have h := atom0678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0679 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0679 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0679 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0679_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283317992349552 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679Coded : CoefficientMerge.Poly := [(nat_lit 831, Int.ofNat (nat_lit 1))]
theorem atom0679Coded_decode : atom0679 = SparsePolynomial.decodeCubic 24 atom0679Coded := by decide +kernel
theorem atom0679Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) := by
  have h := atom0679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0680 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0680 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0680 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0680_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266231762147952 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680Coded : CoefficientMerge.Poly := [(nat_lit 832, Int.ofNat (nat_lit 1))]
theorem atom0680Coded_decode : atom0680 = SparsePolynomial.decodeCubic 24 atom0680Coded := by decide +kernel
theorem atom0680Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded) := by
  have h := atom0680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0681 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0681 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0681 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0681_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264044639632752 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681Coded : CoefficientMerge.Poly := [(nat_lit 833, Int.ofNat (nat_lit 1))]
theorem atom0681Coded_decode : atom0681 = SparsePolynomial.decodeCubic 24 atom0681Coded := by decide +kernel
theorem atom0681Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) := by
  have h := atom0681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0682 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0682 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0682 = ((g 1) * (g 10) * (g 18)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0682_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (313809511246704 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682Coded : CoefficientMerge.Poly := [(nat_lit 834, Int.ofNat (nat_lit 1))]
theorem atom0682Coded_decode : atom0682 = SparsePolynomial.decodeCubic 24 atom0682Coded := by decide +kernel
theorem atom0682Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) := by
  have h := atom0682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0683 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0683 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0683 = ((g 1) * (g 10) * (g 19)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0683_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287349206660208 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683Coded : CoefficientMerge.Poly := [(nat_lit 835, Int.ofNat (nat_lit 1))]
theorem atom0683Coded_decode : atom0683 = SparsePolynomial.decodeCubic 24 atom0683Coded := by decide +kernel
theorem atom0683Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded) := by
  have h := atom0683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0684 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0684 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0684 = ((g 1) * (g 10) * (g 20)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0684_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337773555334512 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684Coded : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 1))]
theorem atom0684Coded_decode : atom0684 = SparsePolynomial.decodeCubic 24 atom0684Coded := by decide +kernel
theorem atom0684Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) := by
  have h := atom0684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0685 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0685 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0685 = ((g 1) * (g 10) * (g 21)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0685_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (333922903467120 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685Coded : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 1))]
theorem atom0685Coded_decode : atom0685 = SparsePolynomial.decodeCubic 24 atom0685Coded := by decide +kernel
theorem atom0685Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded) := by
  have h := atom0685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0686 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0686 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0686 = ((g 1) * (g 10) * (g 22)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0686_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349580333168640 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686Coded : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 1))]
theorem atom0686Coded_decode : atom0686 = SparsePolynomial.decodeCubic 24 atom0686Coded := by decide +kernel
theorem atom0686Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) := by
  have h := atom0686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0687 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0687 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0687 = ((g 1) * (g 10) * (g 23)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0687_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338789442631680 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687Coded : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 1))]
theorem atom0687Coded_decode : atom0687 = SparsePolynomial.decodeCubic 24 atom0687Coded := by decide +kernel
theorem atom0687Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) := by
  have h := atom0687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0688 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0688 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0688 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0688_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201506544866880 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688Coded : CoefficientMerge.Poly := [(nat_lit 851, Int.ofNat (nat_lit 1))]
theorem atom0688Coded_decode : atom0688 = SparsePolynomial.decodeCubic 24 atom0688Coded := by decide +kernel
theorem atom0688Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded) := by
  have h := atom0688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block010 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400)), (nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720)), (nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000)), (nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200)), (nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800)), (nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984)), (nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552)), (nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
def block010_data_flat000 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040))]
theorem block010_data_flat000_step : block010_data_flat000 = (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) := by decide +kernel
theorem block010_data_flat000_original : block010_data_flat000 = (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) := by
  rw [block010_data_flat000_step]
def block010_data_flat001 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 121344224601600))]
theorem block010_data_flat001_step : block010_data_flat001 = (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded) := by decide +kernel
theorem block010_data_flat001_original : block010_data_flat001 = (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded) := by
  rw [block010_data_flat001_step]
def block010_data_flat002 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600))]
theorem block010_data_flat002_step : block010_data_flat002 = (CoefficientMerge.fastMerge block010_data_flat000 block010_data_flat001) := by decide +kernel
theorem block010_data_flat002_original : block010_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) := by
  rw [block010_data_flat002_step, block010_data_flat000_original, block010_data_flat001_original]
def block010_data_flat003 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 129213729335592))]
theorem block010_data_flat003_step : block010_data_flat003 = (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) := by decide +kernel
theorem block010_data_flat003_original : block010_data_flat003 = (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) := by
  rw [block010_data_flat003_step]
def block010_data_flat004 : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 156989643019704))]
theorem block010_data_flat004_step : block010_data_flat004 = (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) := by decide +kernel
theorem block010_data_flat004_original : block010_data_flat004 = (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) := by
  rw [block010_data_flat004_step]
def block010_data_flat005 : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 178123796942256))]
theorem block010_data_flat005_step : block010_data_flat005 = (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded) := by decide +kernel
theorem block010_data_flat005_original : block010_data_flat005 = (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded) := by
  rw [block010_data_flat005_step]
def block010_data_flat006 : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256))]
theorem block010_data_flat006_step : block010_data_flat006 = (CoefficientMerge.fastMerge block010_data_flat004 block010_data_flat005) := by decide +kernel
theorem block010_data_flat006_original : block010_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)) := by
  rw [block010_data_flat006_step, block010_data_flat004_original, block010_data_flat005_original]
def block010_data_flat007 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256))]
theorem block010_data_flat007_step : block010_data_flat007 = (CoefficientMerge.fastMerge block010_data_flat003 block010_data_flat006) := by decide +kernel
theorem block010_data_flat007_original : block010_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded))) := by
  rw [block010_data_flat007_step, block010_data_flat003_original, block010_data_flat006_original]
def block010_data_flat008 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256))]
theorem block010_data_flat008_step : block010_data_flat008 = (CoefficientMerge.fastMerge block010_data_flat002 block010_data_flat007) := by decide +kernel
theorem block010_data_flat008_original : block010_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) := by
  rw [block010_data_flat008_step, block010_data_flat002_original, block010_data_flat007_original]
def block010_data_flat009 : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 218964915186336))]
theorem block010_data_flat009_step : block010_data_flat009 = (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) := by decide +kernel
theorem block010_data_flat009_original : block010_data_flat009 = (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) := by
  rw [block010_data_flat009_step]
def block010_data_flat010 : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 205962588216000))]
theorem block010_data_flat010_step : block010_data_flat010 = (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded) := by decide +kernel
theorem block010_data_flat010_original : block010_data_flat010 = (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded) := by
  rw [block010_data_flat010_step]
def block010_data_flat011 : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000))]
theorem block010_data_flat011_step : block010_data_flat011 = (CoefficientMerge.fastMerge block010_data_flat009 block010_data_flat010) := by decide +kernel
theorem block010_data_flat011_original : block010_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) := by
  rw [block010_data_flat011_step, block010_data_flat009_original, block010_data_flat010_original]
def block010_data_flat012 : CoefficientMerge.Poly := [(nat_lit 734, Int.ofNat (nat_lit 187448867020800))]
theorem block010_data_flat012_step : block010_data_flat012 = (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) := by decide +kernel
theorem block010_data_flat012_original : block010_data_flat012 = (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) := by
  rw [block010_data_flat012_step]
def block010_data_flat013 : CoefficientMerge.Poly := [(nat_lit 735, Int.ofNat (nat_lit 191115655718400))]
theorem block010_data_flat013_step : block010_data_flat013 = (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) := by decide +kernel
theorem block010_data_flat013_original : block010_data_flat013 = (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) := by
  rw [block010_data_flat013_step]
def block010_data_flat014 : CoefficientMerge.Poly := [(nat_lit 736, Int.ofNat (nat_lit 177048679046400))]
theorem block010_data_flat014_step : block010_data_flat014 = (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded) := by decide +kernel
theorem block010_data_flat014_original : block010_data_flat014 = (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded) := by
  rw [block010_data_flat014_step]
def block010_data_flat015 : CoefficientMerge.Poly := [(nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400))]
theorem block010_data_flat015_step : block010_data_flat015 = (CoefficientMerge.fastMerge block010_data_flat013 block010_data_flat014) := by decide +kernel
theorem block010_data_flat015_original : block010_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded)) := by
  rw [block010_data_flat015_step, block010_data_flat013_original, block010_data_flat014_original]
def block010_data_flat016 : CoefficientMerge.Poly := [(nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400))]
theorem block010_data_flat016_step : block010_data_flat016 = (CoefficientMerge.fastMerge block010_data_flat012 block010_data_flat015) := by decide +kernel
theorem block010_data_flat016_original : block010_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))) := by
  rw [block010_data_flat016_step, block010_data_flat012_original, block010_data_flat015_original]
def block010_data_flat017 : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400))]
theorem block010_data_flat017_step : block010_data_flat017 = (CoefficientMerge.fastMerge block010_data_flat011 block010_data_flat016) := by decide +kernel
theorem block010_data_flat017_original : block010_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded)))) := by
  rw [block010_data_flat017_step, block010_data_flat011_original, block010_data_flat016_original]
def block010_data_flat018 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400))]
theorem block010_data_flat018_step : block010_data_flat018 = (CoefficientMerge.fastMerge block010_data_flat008 block010_data_flat017) := by decide +kernel
theorem block010_data_flat018_original : block010_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) := by
  rw [block010_data_flat018_step, block010_data_flat008_original, block010_data_flat017_original]
def block010_data_flat019 : CoefficientMerge.Poly := [(nat_lit 737, Int.ofNat (nat_lit 177880810060800))]
theorem block010_data_flat019_step : block010_data_flat019 = (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) := by decide +kernel
theorem block010_data_flat019_original : block010_data_flat019 = (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) := by
  rw [block010_data_flat019_step]
def block010_data_flat020 : CoefficientMerge.Poly := [(nat_lit 738, Int.ofNat (nat_lit 227305139846400))]
theorem block010_data_flat020_step : block010_data_flat020 = (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded) := by decide +kernel
theorem block010_data_flat020_original : block010_data_flat020 = (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded) := by
  rw [block010_data_flat020_step]
def block010_data_flat021 : CoefficientMerge.Poly := [(nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400))]
theorem block010_data_flat021_step : block010_data_flat021 = (CoefficientMerge.fastMerge block010_data_flat019 block010_data_flat020) := by decide +kernel
theorem block010_data_flat021_original : block010_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) := by
  rw [block010_data_flat021_step, block010_data_flat019_original, block010_data_flat020_original]
def block010_data_flat022 : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 197144498073600))]
theorem block010_data_flat022_step : block010_data_flat022 = (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) := by decide +kernel
theorem block010_data_flat022_original : block010_data_flat022 = (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) := by
  rw [block010_data_flat022_step]
def block010_data_flat023 : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 243868509561600))]
theorem block010_data_flat023_step : block010_data_flat023 = (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) := by decide +kernel
theorem block010_data_flat023_original : block010_data_flat023 = (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) := by
  rw [block010_data_flat023_step]
def block010_data_flat024 : CoefficientMerge.Poly := [(nat_lit 741, Int.ofNat (nat_lit 229597929792000))]
theorem block010_data_flat024_step : block010_data_flat024 = (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded) := by decide +kernel
theorem block010_data_flat024_original : block010_data_flat024 = (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded) := by
  rw [block010_data_flat024_step]
def block010_data_flat025 : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000))]
theorem block010_data_flat025_step : block010_data_flat025 = (CoefficientMerge.fastMerge block010_data_flat023 block010_data_flat024) := by decide +kernel
theorem block010_data_flat025_original : block010_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)) := by
  rw [block010_data_flat025_step, block010_data_flat023_original, block010_data_flat024_original]
def block010_data_flat026 : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000))]
theorem block010_data_flat026_step : block010_data_flat026 = (CoefficientMerge.fastMerge block010_data_flat022 block010_data_flat025) := by decide +kernel
theorem block010_data_flat026_original : block010_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded))) := by
  rw [block010_data_flat026_step, block010_data_flat022_original, block010_data_flat025_original]
def block010_data_flat027 : CoefficientMerge.Poly := [(nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000))]
theorem block010_data_flat027_step : block010_data_flat027 = (CoefficientMerge.fastMerge block010_data_flat021 block010_data_flat026) := by decide +kernel
theorem block010_data_flat027_original : block010_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) := by
  rw [block010_data_flat027_step, block010_data_flat021_original, block010_data_flat026_original]
def block010_data_flat028 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 292791670752000))]
theorem block010_data_flat028_step : block010_data_flat028 = (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) := by decide +kernel
theorem block010_data_flat028_original : block010_data_flat028 = (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) := by
  rw [block010_data_flat028_step]
def block010_data_flat029 : CoefficientMerge.Poly := [(nat_lit 743, Int.ofNat (nat_lit 280178158176000))]
theorem block010_data_flat029_step : block010_data_flat029 = (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded) := by decide +kernel
theorem block010_data_flat029_original : block010_data_flat029 = (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded) := by
  rw [block010_data_flat029_step]
def block010_data_flat030 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000))]
theorem block010_data_flat030_step : block010_data_flat030 = (CoefficientMerge.fastMerge block010_data_flat028 block010_data_flat029) := by decide +kernel
theorem block010_data_flat030_original : block010_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) := by
  rw [block010_data_flat030_step, block010_data_flat028_original, block010_data_flat029_original]
def block010_data_flat031 : CoefficientMerge.Poly := [(nat_lit 751, Int.ofNat (nat_lit 97409907302400))]
theorem block010_data_flat031_step : block010_data_flat031 = (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) := by decide +kernel
theorem block010_data_flat031_original : block010_data_flat031 = (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) := by
  rw [block010_data_flat031_step]
def block010_data_flat032 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 166327558467840))]
theorem block010_data_flat032_step : block010_data_flat032 = (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) := by decide +kernel
theorem block010_data_flat032_original : block010_data_flat032 = (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) := by
  rw [block010_data_flat032_step]
def block010_data_flat033 : CoefficientMerge.Poly := [(nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat033_step : block010_data_flat033 = (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded) := by decide +kernel
theorem block010_data_flat033_original : block010_data_flat033 = (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded) := by
  rw [block010_data_flat033_step]
def block010_data_flat034 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat034_step : block010_data_flat034 = (CoefficientMerge.fastMerge block010_data_flat032 block010_data_flat033) := by decide +kernel
theorem block010_data_flat034_original : block010_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)) := by
  rw [block010_data_flat034_step, block010_data_flat032_original, block010_data_flat033_original]
def block010_data_flat035 : CoefficientMerge.Poly := [(nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat035_step : block010_data_flat035 = (CoefficientMerge.fastMerge block010_data_flat031 block010_data_flat034) := by decide +kernel
theorem block010_data_flat035_original : block010_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded))) := by
  rw [block010_data_flat035_step, block010_data_flat031_original, block010_data_flat034_original]
def block010_data_flat036 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat036_step : block010_data_flat036 = (CoefficientMerge.fastMerge block010_data_flat030 block010_data_flat035) := by decide +kernel
theorem block010_data_flat036_original : block010_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))) := by
  rw [block010_data_flat036_step, block010_data_flat030_original, block010_data_flat035_original]
def block010_data_flat037 : CoefficientMerge.Poly := [(nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat037_step : block010_data_flat037 = (CoefficientMerge.fastMerge block010_data_flat027 block010_data_flat036) := by decide +kernel
theorem block010_data_flat037_original : block010_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded))))) := by
  rw [block010_data_flat037_step, block010_data_flat027_original, block010_data_flat036_original]
def block010_data_flat038 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400)), (nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720))]
theorem block010_data_flat038_step : block010_data_flat038 = (CoefficientMerge.fastMerge block010_data_flat018 block010_data_flat037) := by decide +kernel
theorem block010_data_flat038_original : block010_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))))) := by
  rw [block010_data_flat038_step, block010_data_flat018_original, block010_data_flat037_original]
def block010_data_flat039 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 170879862994104))]
theorem block010_data_flat039_step : block010_data_flat039 = (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) := by decide +kernel
theorem block010_data_flat039_original : block010_data_flat039 = (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) := by
  rw [block010_data_flat039_step]
def block010_data_flat040 : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 193055872007856))]
theorem block010_data_flat040_step : block010_data_flat040 = (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded) := by decide +kernel
theorem block010_data_flat040_original : block010_data_flat040 = (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded) := by
  rw [block010_data_flat040_step]
def block010_data_flat041 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856))]
theorem block010_data_flat041_step : block010_data_flat041 = (CoefficientMerge.fastMerge block010_data_flat039 block010_data_flat040) := by decide +kernel
theorem block010_data_flat041_original : block010_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) := by
  rw [block010_data_flat041_step, block010_data_flat039_original, block010_data_flat040_original]
def block010_data_flat042 : CoefficientMerge.Poly := [(nat_lit 756, Int.ofNat (nat_lit 234938845343136))]
theorem block010_data_flat042_step : block010_data_flat042 = (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) := by decide +kernel
theorem block010_data_flat042_original : block010_data_flat042 = (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) := by
  rw [block010_data_flat042_step]
def block010_data_flat043 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 221947149547200))]
theorem block010_data_flat043_step : block010_data_flat043 = (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) := by decide +kernel
theorem block010_data_flat043_original : block010_data_flat043 = (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) := by
  rw [block010_data_flat043_step]
def block010_data_flat044 : CoefficientMerge.Poly := [(nat_lit 758, Int.ofNat (nat_lit 203444059526400))]
theorem block010_data_flat044_step : block010_data_flat044 = (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded) := by decide +kernel
theorem block010_data_flat044_original : block010_data_flat044 = (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded) := by
  rw [block010_data_flat044_step]
def block010_data_flat045 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400))]
theorem block010_data_flat045_step : block010_data_flat045 = (CoefficientMerge.fastMerge block010_data_flat043 block010_data_flat044) := by decide +kernel
theorem block010_data_flat045_original : block010_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)) := by
  rw [block010_data_flat045_step, block010_data_flat043_original, block010_data_flat044_original]
def block010_data_flat046 : CoefficientMerge.Poly := [(nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400))]
theorem block010_data_flat046_step : block010_data_flat046 = (CoefficientMerge.fastMerge block010_data_flat042 block010_data_flat045) := by decide +kernel
theorem block010_data_flat046_original : block010_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded))) := by
  rw [block010_data_flat046_step, block010_data_flat042_original, block010_data_flat045_original]
def block010_data_flat047 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400))]
theorem block010_data_flat047_step : block010_data_flat047 = (CoefficientMerge.fastMerge block010_data_flat041 block010_data_flat046) := by decide +kernel
theorem block010_data_flat047_original : block010_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) := by
  rw [block010_data_flat047_step, block010_data_flat041_original, block010_data_flat046_original]
def block010_data_flat048 : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 207121479398400))]
theorem block010_data_flat048_step : block010_data_flat048 = (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) := by decide +kernel
theorem block010_data_flat048_original : block010_data_flat048 = (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) := by
  rw [block010_data_flat048_step]
def block010_data_flat049 : CoefficientMerge.Poly := [(nat_lit 760, Int.ofNat (nat_lit 193065133900800))]
theorem block010_data_flat049_step : block010_data_flat049 = (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded) := by decide +kernel
theorem block010_data_flat049_original : block010_data_flat049 = (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded) := by
  rw [block010_data_flat049_step]
def block010_data_flat050 : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800))]
theorem block010_data_flat050_step : block010_data_flat050 = (CoefficientMerge.fastMerge block010_data_flat048 block010_data_flat049) := by decide +kernel
theorem block010_data_flat050_original : block010_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) := by
  rw [block010_data_flat050_step, block010_data_flat048_original, block010_data_flat049_original]
def block010_data_flat051 : CoefficientMerge.Poly := [(nat_lit 761, Int.ofNat (nat_lit 193907896089600))]
theorem block010_data_flat051_step : block010_data_flat051 = (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) := by decide +kernel
theorem block010_data_flat051_original : block010_data_flat051 = (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) := by
  rw [block010_data_flat051_step]
def block010_data_flat052 : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 244507561267200))]
theorem block010_data_flat052_step : block010_data_flat052 = (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) := by decide +kernel
theorem block010_data_flat052_original : block010_data_flat052 = (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) := by
  rw [block010_data_flat052_step]
def block010_data_flat053 : CoefficientMerge.Poly := [(nat_lit 763, Int.ofNat (nat_lit 216686959104000))]
theorem block010_data_flat053_step : block010_data_flat053 = (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded) := by decide +kernel
theorem block010_data_flat053_original : block010_data_flat053 = (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded) := by
  rw [block010_data_flat053_step]
def block010_data_flat054 : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000))]
theorem block010_data_flat054_step : block010_data_flat054 = (CoefficientMerge.fastMerge block010_data_flat052 block010_data_flat053) := by decide +kernel
theorem block010_data_flat054_original : block010_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded)) := by
  rw [block010_data_flat054_step, block010_data_flat052_original, block010_data_flat053_original]
def block010_data_flat055 : CoefficientMerge.Poly := [(nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000))]
theorem block010_data_flat055_step : block010_data_flat055 = (CoefficientMerge.fastMerge block010_data_flat051 block010_data_flat054) := by decide +kernel
theorem block010_data_flat055_original : block010_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))) := by
  rw [block010_data_flat055_step, block010_data_flat051_original, block010_data_flat054_original]
def block010_data_flat056 : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000))]
theorem block010_data_flat056_step : block010_data_flat056 = (CoefficientMerge.fastMerge block010_data_flat050 block010_data_flat055) := by decide +kernel
theorem block010_data_flat056_original : block010_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded)))) := by
  rw [block010_data_flat056_step, block010_data_flat050_original, block010_data_flat055_original]
def block010_data_flat057 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000))]
theorem block010_data_flat057_step : block010_data_flat057 = (CoefficientMerge.fastMerge block010_data_flat047 block010_data_flat056) := by decide +kernel
theorem block010_data_flat057_original : block010_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) := by
  rw [block010_data_flat057_step, block010_data_flat047_original, block010_data_flat056_original]
def block010_data_flat058 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 265751010201600))]
theorem block010_data_flat058_step : block010_data_flat058 = (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) := by decide +kernel
theorem block010_data_flat058_original : block010_data_flat058 = (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) := by
  rw [block010_data_flat058_step]
def block010_data_flat059 : CoefficientMerge.Poly := [(nat_lit 765, Int.ofNat (nat_lit 256149878476800))]
theorem block010_data_flat059_step : block010_data_flat059 = (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded) := by decide +kernel
theorem block010_data_flat059_original : block010_data_flat059 = (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded) := by
  rw [block010_data_flat059_step]
def block010_data_flat060 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800))]
theorem block010_data_flat060_step : block010_data_flat060 = (CoefficientMerge.fastMerge block010_data_flat058 block010_data_flat059) := by decide +kernel
theorem block010_data_flat060_original : block010_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) := by
  rw [block010_data_flat060_step, block010_data_flat058_original, block010_data_flat059_original]
def block010_data_flat061 : CoefficientMerge.Poly := [(nat_lit 766, Int.ofNat (nat_lit 326703148352000))]
theorem block010_data_flat061_step : block010_data_flat061 = (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) := by decide +kernel
theorem block010_data_flat061_original : block010_data_flat061 = (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) := by
  rw [block010_data_flat061_step]
def block010_data_flat062 : CoefficientMerge.Poly := [(nat_lit 767, Int.ofNat (nat_lit 316265679676800))]
theorem block010_data_flat062_step : block010_data_flat062 = (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) := by decide +kernel
theorem block010_data_flat062_original : block010_data_flat062 = (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) := by
  rw [block010_data_flat062_step]
def block010_data_flat063 : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 113923664870400))]
theorem block010_data_flat063_step : block010_data_flat063 = (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded) := by decide +kernel
theorem block010_data_flat063_original : block010_data_flat063 = (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded) := by
  rw [block010_data_flat063_step]
def block010_data_flat064 : CoefficientMerge.Poly := [(nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400))]
theorem block010_data_flat064_step : block010_data_flat064 = (CoefficientMerge.fastMerge block010_data_flat062 block010_data_flat063) := by decide +kernel
theorem block010_data_flat064_original : block010_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)) := by
  rw [block010_data_flat064_step, block010_data_flat062_original, block010_data_flat063_original]
def block010_data_flat065 : CoefficientMerge.Poly := [(nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400))]
theorem block010_data_flat065_step : block010_data_flat065 = (CoefficientMerge.fastMerge block010_data_flat061 block010_data_flat064) := by decide +kernel
theorem block010_data_flat065_original : block010_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded))) := by
  rw [block010_data_flat065_step, block010_data_flat061_original, block010_data_flat064_original]
def block010_data_flat066 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400))]
theorem block010_data_flat066_step : block010_data_flat066 = (CoefficientMerge.fastMerge block010_data_flat060 block010_data_flat065) := by decide +kernel
theorem block010_data_flat066_original : block010_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) := by
  rw [block010_data_flat066_step, block010_data_flat060_original, block010_data_flat065_original]
def block010_data_flat067 : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 204854516840160))]
theorem block010_data_flat067_step : block010_data_flat067 = (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) := by decide +kernel
theorem block010_data_flat067_original : block010_data_flat067 = (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) := by
  rw [block010_data_flat067_step]
def block010_data_flat068 : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 188840203618968))]
theorem block010_data_flat068_step : block010_data_flat068 = (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded) := by decide +kernel
theorem block010_data_flat068_original : block010_data_flat068 = (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded) := by
  rw [block010_data_flat068_step]
def block010_data_flat069 : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968))]
theorem block010_data_flat069_step : block010_data_flat069 = (CoefficientMerge.fastMerge block010_data_flat067 block010_data_flat068) := by decide +kernel
theorem block010_data_flat069_original : block010_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) := by
  rw [block010_data_flat069_step, block010_data_flat067_original, block010_data_flat068_original]
def block010_data_flat070 : CoefficientMerge.Poly := [(nat_lit 779, Int.ofNat (nat_lit 207125640705456))]
theorem block010_data_flat070_step : block010_data_flat070 = (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) := by decide +kernel
theorem block010_data_flat070_original : block010_data_flat070 = (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) := by
  rw [block010_data_flat070_step]
def block010_data_flat071 : CoefficientMerge.Poly := [(nat_lit 780, Int.ofNat (nat_lit 246967428555936))]
theorem block010_data_flat071_step : block010_data_flat071 = (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) := by decide +kernel
theorem block010_data_flat071_original : block010_data_flat071 = (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) := by
  rw [block010_data_flat071_step]
def block010_data_flat072 : CoefficientMerge.Poly := [(nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat072_step : block010_data_flat072 = (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded) := by decide +kernel
theorem block010_data_flat072_original : block010_data_flat072 = (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded) := by
  rw [block010_data_flat072_step]
def block010_data_flat073 : CoefficientMerge.Poly := [(nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat073_step : block010_data_flat073 = (CoefficientMerge.fastMerge block010_data_flat071 block010_data_flat072) := by decide +kernel
theorem block010_data_flat073_original : block010_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded)) := by
  rw [block010_data_flat073_step, block010_data_flat071_original, block010_data_flat072_original]
def block010_data_flat074 : CoefficientMerge.Poly := [(nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat074_step : block010_data_flat074 = (CoefficientMerge.fastMerge block010_data_flat070 block010_data_flat073) := by decide +kernel
theorem block010_data_flat074_original : block010_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))) := by
  rw [block010_data_flat074_step, block010_data_flat070_original, block010_data_flat073_original]
def block010_data_flat075 : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat075_step : block010_data_flat075 = (CoefficientMerge.fastMerge block010_data_flat069 block010_data_flat074) := by decide +kernel
theorem block010_data_flat075_original : block010_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded)))) := by
  rw [block010_data_flat075_step, block010_data_flat069_original, block010_data_flat074_original]
def block010_data_flat076 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat076_step : block010_data_flat076 = (CoefficientMerge.fastMerge block010_data_flat066 block010_data_flat075) := by decide +kernel
theorem block010_data_flat076_original : block010_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))))) := by
  rw [block010_data_flat076_step, block010_data_flat066_original, block010_data_flat075_original]
def block010_data_flat077 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000)), (nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat077_step : block010_data_flat077 = (CoefficientMerge.fastMerge block010_data_flat057 block010_data_flat076) := by decide +kernel
theorem block010_data_flat077_original : block010_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded)))))) := by
  rw [block010_data_flat077_step, block010_data_flat057_original, block010_data_flat076_original]
def block010_data_flat078 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400)), (nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720)), (nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000)), (nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200))]
theorem block010_data_flat078_step : block010_data_flat078 = (CoefficientMerge.fastMerge block010_data_flat038 block010_data_flat077) := by decide +kernel
theorem block010_data_flat078_original : block010_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))))))) := by
  rw [block010_data_flat078_step, block010_data_flat038_original, block010_data_flat077_original]
def block010_data_flat079 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600))]
theorem block010_data_flat079_step : block010_data_flat079 = (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) := by decide +kernel
theorem block010_data_flat079_original : block010_data_flat079 = (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) := by
  rw [block010_data_flat079_step]
def block010_data_flat080 : CoefficientMerge.Poly := [(nat_lit 783, Int.ofNat (nat_lit 217651067020800))]
theorem block010_data_flat080_step : block010_data_flat080 = (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded) := by decide +kernel
theorem block010_data_flat080_original : block010_data_flat080 = (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded) := by
  rw [block010_data_flat080_step]
def block010_data_flat081 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800))]
theorem block010_data_flat081_step : block010_data_flat081 = (CoefficientMerge.fastMerge block010_data_flat079 block010_data_flat080) := by decide +kernel
theorem block010_data_flat081_original : block010_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) := by
  rw [block010_data_flat081_step, block010_data_flat079_original, block010_data_flat080_original]
def block010_data_flat082 : CoefficientMerge.Poly := [(nat_lit 784, Int.ofNat (nat_lit 203095056326400))]
theorem block010_data_flat082_step : block010_data_flat082 = (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) := by decide +kernel
theorem block010_data_flat082_original : block010_data_flat082 = (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) := by
  rw [block010_data_flat082_step]
def block010_data_flat083 : CoefficientMerge.Poly := [(nat_lit 785, Int.ofNat (nat_lit 203438153318400))]
theorem block010_data_flat083_step : block010_data_flat083 = (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) := by decide +kernel
theorem block010_data_flat083_original : block010_data_flat083 = (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) := by
  rw [block010_data_flat083_step]
def block010_data_flat084 : CoefficientMerge.Poly := [(nat_lit 786, Int.ofNat (nat_lit 255265128518400))]
theorem block010_data_flat084_step : block010_data_flat084 = (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded) := by decide +kernel
theorem block010_data_flat084_original : block010_data_flat084 = (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded) := by
  rw [block010_data_flat084_step]
def block010_data_flat085 : CoefficientMerge.Poly := [(nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400))]
theorem block010_data_flat085_step : block010_data_flat085 = (CoefficientMerge.fastMerge block010_data_flat083 block010_data_flat084) := by decide +kernel
theorem block010_data_flat085_original : block010_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)) := by
  rw [block010_data_flat085_step, block010_data_flat083_original, block010_data_flat084_original]
def block010_data_flat086 : CoefficientMerge.Poly := [(nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400))]
theorem block010_data_flat086_step : block010_data_flat086 = (CoefficientMerge.fastMerge block010_data_flat082 block010_data_flat085) := by decide +kernel
theorem block010_data_flat086_original : block010_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded))) := by
  rw [block010_data_flat086_step, block010_data_flat082_original, block010_data_flat085_original]
def block010_data_flat087 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400))]
theorem block010_data_flat087_step : block010_data_flat087 = (CoefficientMerge.fastMerge block010_data_flat081 block010_data_flat086) := by decide +kernel
theorem block010_data_flat087_original : block010_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) := by
  rw [block010_data_flat087_step, block010_data_flat081_original, block010_data_flat086_original]
def block010_data_flat088 : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 230398811596800))]
theorem block010_data_flat088_step : block010_data_flat088 = (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) := by decide +kernel
theorem block010_data_flat088_original : block010_data_flat088 = (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) := by
  rw [block010_data_flat088_step]
def block010_data_flat089 : CoefficientMerge.Poly := [(nat_lit 788, Int.ofNat (nat_lit 282417147936000))]
theorem block010_data_flat089_step : block010_data_flat089 = (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded) := by decide +kernel
theorem block010_data_flat089_original : block010_data_flat089 = (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded) := by
  rw [block010_data_flat089_step]
def block010_data_flat090 : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000))]
theorem block010_data_flat090_step : block010_data_flat090 = (CoefficientMerge.fastMerge block010_data_flat088 block010_data_flat089) := by decide +kernel
theorem block010_data_flat090_original : block010_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) := by
  rw [block010_data_flat090_step, block010_data_flat088_original, block010_data_flat089_original]
def block010_data_flat091 : CoefficientMerge.Poly := [(nat_lit 789, Int.ofNat (nat_lit 279224251891200))]
theorem block010_data_flat091_step : block010_data_flat091 = (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) := by decide +kernel
theorem block010_data_flat091_original : block010_data_flat091 = (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) := by
  rw [block010_data_flat091_step]
def block010_data_flat092 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 356557454803200))]
theorem block010_data_flat092_step : block010_data_flat092 = (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) := by decide +kernel
theorem block010_data_flat092_original : block010_data_flat092 = (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) := by
  rw [block010_data_flat092_step]
def block010_data_flat093 : CoefficientMerge.Poly := [(nat_lit 791, Int.ofNat (nat_lit 349745019724800))]
theorem block010_data_flat093_step : block010_data_flat093 = (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded) := by decide +kernel
theorem block010_data_flat093_original : block010_data_flat093 = (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded) := by
  rw [block010_data_flat093_step]
def block010_data_flat094 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800))]
theorem block010_data_flat094_step : block010_data_flat094 = (CoefficientMerge.fastMerge block010_data_flat092 block010_data_flat093) := by decide +kernel
theorem block010_data_flat094_original : block010_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded)) := by
  rw [block010_data_flat094_step, block010_data_flat092_original, block010_data_flat093_original]
def block010_data_flat095 : CoefficientMerge.Poly := [(nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800))]
theorem block010_data_flat095_step : block010_data_flat095 = (CoefficientMerge.fastMerge block010_data_flat091 block010_data_flat094) := by decide +kernel
theorem block010_data_flat095_original : block010_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))) := by
  rw [block010_data_flat095_step, block010_data_flat091_original, block010_data_flat094_original]
def block010_data_flat096 : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800))]
theorem block010_data_flat096_step : block010_data_flat096 = (CoefficientMerge.fastMerge block010_data_flat090 block010_data_flat095) := by decide +kernel
theorem block010_data_flat096_original : block010_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded)))) := by
  rw [block010_data_flat096_step, block010_data_flat090_original, block010_data_flat095_original]
def block010_data_flat097 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800))]
theorem block010_data_flat097_step : block010_data_flat097 = (CoefficientMerge.fastMerge block010_data_flat087 block010_data_flat096) := by decide +kernel
theorem block010_data_flat097_original : block010_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) := by
  rw [block010_data_flat097_step, block010_data_flat087_original, block010_data_flat096_original]
def block010_data_flat098 : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 136999274369760))]
theorem block010_data_flat098_step : block010_data_flat098 = (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) := by decide +kernel
theorem block010_data_flat098_original : block010_data_flat098 = (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) := by
  rw [block010_data_flat098_step]
def block010_data_flat099 : CoefficientMerge.Poly := [(nat_lit 802, Int.ofNat (nat_lit 255486130384320))]
theorem block010_data_flat099_step : block010_data_flat099 = (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded) := by decide +kernel
theorem block010_data_flat099_original : block010_data_flat099 = (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded) := by
  rw [block010_data_flat099_step]
def block010_data_flat100 : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320))]
theorem block010_data_flat100_step : block010_data_flat100 = (CoefficientMerge.fastMerge block010_data_flat098 block010_data_flat099) := by decide +kernel
theorem block010_data_flat100_original : block010_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) := by
  rw [block010_data_flat100_step, block010_data_flat098_original, block010_data_flat099_original]
def block010_data_flat101 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 242659403316000))]
theorem block010_data_flat101_step : block010_data_flat101 = (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) := by decide +kernel
theorem block010_data_flat101_original : block010_data_flat101 = (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) := by
  rw [block010_data_flat101_step]
def block010_data_flat102 : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 272104064602128))]
theorem block010_data_flat102_step : block010_data_flat102 = (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) := by decide +kernel
theorem block010_data_flat102_original : block010_data_flat102 = (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) := by
  rw [block010_data_flat102_step]
def block010_data_flat103 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 256061221753392))]
theorem block010_data_flat103_step : block010_data_flat103 = (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded) := by decide +kernel
theorem block010_data_flat103_original : block010_data_flat103 = (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded) := by
  rw [block010_data_flat103_step]
def block010_data_flat104 : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392))]
theorem block010_data_flat104_step : block010_data_flat104 = (CoefficientMerge.fastMerge block010_data_flat102 block010_data_flat103) := by decide +kernel
theorem block010_data_flat104_original : block010_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)) := by
  rw [block010_data_flat104_step, block010_data_flat102_original, block010_data_flat103_original]
def block010_data_flat105 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392))]
theorem block010_data_flat105_step : block010_data_flat105 = (CoefficientMerge.fastMerge block010_data_flat101 block010_data_flat104) := by decide +kernel
theorem block010_data_flat105_original : block010_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded))) := by
  rw [block010_data_flat105_step, block010_data_flat101_original, block010_data_flat104_original]
def block010_data_flat106 : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392))]
theorem block010_data_flat106_step : block010_data_flat106 = (CoefficientMerge.fastMerge block010_data_flat100 block010_data_flat105) := by decide +kernel
theorem block010_data_flat106_original : block010_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) := by
  rw [block010_data_flat106_step, block010_data_flat100_original, block010_data_flat105_original]
def block010_data_flat107 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 236048504967792))]
theorem block010_data_flat107_step : block010_data_flat107 = (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) := by decide +kernel
theorem block010_data_flat107_original : block010_data_flat107 = (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) := by
  rw [block010_data_flat107_step]
def block010_data_flat108 : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 238216298074992))]
theorem block010_data_flat108_step : block010_data_flat108 = (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded) := by decide +kernel
theorem block010_data_flat108_original : block010_data_flat108 = (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded) := by
  rw [block010_data_flat108_step]
def block010_data_flat109 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992))]
theorem block010_data_flat109_step : block010_data_flat109 = (CoefficientMerge.fastMerge block010_data_flat107 block010_data_flat108) := by decide +kernel
theorem block010_data_flat109_original : block010_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) := by
  rw [block010_data_flat109_step, block010_data_flat107_original, block010_data_flat108_original]
def block010_data_flat110 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 222650325812592))]
theorem block010_data_flat110_step : block010_data_flat110 = (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) := by decide +kernel
theorem block010_data_flat110_original : block010_data_flat110 = (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) := by
  rw [block010_data_flat110_step]
def block010_data_flat111 : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 221983461236592))]
theorem block010_data_flat111_step : block010_data_flat111 = (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) := by decide +kernel
theorem block010_data_flat111_original : block010_data_flat111 = (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) := by
  rw [block010_data_flat111_step]
def block010_data_flat112 : CoefficientMerge.Poly := [(nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat112_step : block010_data_flat112 = (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded) := by decide +kernel
theorem block010_data_flat112_original : block010_data_flat112 = (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded) := by
  rw [block010_data_flat112_step]
def block010_data_flat113 : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat113_step : block010_data_flat113 = (CoefficientMerge.fastMerge block010_data_flat111 block010_data_flat112) := by decide +kernel
theorem block010_data_flat113_original : block010_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)) := by
  rw [block010_data_flat113_step, block010_data_flat111_original, block010_data_flat112_original]
def block010_data_flat114 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat114_step : block010_data_flat114 = (CoefficientMerge.fastMerge block010_data_flat110 block010_data_flat113) := by decide +kernel
theorem block010_data_flat114_original : block010_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded))) := by
  rw [block010_data_flat114_step, block010_data_flat110_original, block010_data_flat113_original]
def block010_data_flat115 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat115_step : block010_data_flat115 = (CoefficientMerge.fastMerge block010_data_flat109 block010_data_flat114) := by decide +kernel
theorem block010_data_flat115_original : block010_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))) := by
  rw [block010_data_flat115_step, block010_data_flat109_original, block010_data_flat114_original]
def block010_data_flat116 : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat116_step : block010_data_flat116 = (CoefficientMerge.fastMerge block010_data_flat106 block010_data_flat115) := by decide +kernel
theorem block010_data_flat116_original : block010_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded))))) := by
  rw [block010_data_flat116_step, block010_data_flat106_original, block010_data_flat115_original]
def block010_data_flat117 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800)), (nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984))]
theorem block010_data_flat117_step : block010_data_flat117 = (CoefficientMerge.fastMerge block010_data_flat097 block010_data_flat116) := by decide +kernel
theorem block010_data_flat117_original : block010_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))))) := by
  rw [block010_data_flat117_step, block010_data_flat097_original, block010_data_flat116_original]
def block010_data_flat118 : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 250229398125168))]
theorem block010_data_flat118_step : block010_data_flat118 = (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) := by decide +kernel
theorem block010_data_flat118_original : block010_data_flat118 = (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) := by
  rw [block010_data_flat118_step]
def block010_data_flat119 : CoefficientMerge.Poly := [(nat_lit 812, Int.ofNat (nat_lit 303441240727152))]
theorem block010_data_flat119_step : block010_data_flat119 = (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded) := by decide +kernel
theorem block010_data_flat119_original : block010_data_flat119 = (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded) := by
  rw [block010_data_flat119_step]
def block010_data_flat120 : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152))]
theorem block010_data_flat120_step : block010_data_flat120 = (CoefficientMerge.fastMerge block010_data_flat118 block010_data_flat119) := by decide +kernel
theorem block010_data_flat120_original : block010_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) := by
  rw [block010_data_flat120_step, block010_data_flat118_original, block010_data_flat119_original]
def block010_data_flat121 : CoefficientMerge.Poly := [(nat_lit 813, Int.ofNat (nat_lit 303645318775920))]
theorem block010_data_flat121_step : block010_data_flat121 = (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) := by decide +kernel
theorem block010_data_flat121_original : block010_data_flat121 = (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) := by
  rw [block010_data_flat121_step]
def block010_data_flat122 : CoefficientMerge.Poly := [(nat_lit 814, Int.ofNat (nat_lit 368500279875840))]
theorem block010_data_flat122_step : block010_data_flat122 = (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) := by decide +kernel
theorem block010_data_flat122_original : block010_data_flat122 = (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) := by
  rw [block010_data_flat122_step]
def block010_data_flat123 : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 362803493738880))]
theorem block010_data_flat123_step : block010_data_flat123 = (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded) := by decide +kernel
theorem block010_data_flat123_original : block010_data_flat123 = (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded) := by
  rw [block010_data_flat123_step]
def block010_data_flat124 : CoefficientMerge.Poly := [(nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880))]
theorem block010_data_flat124_step : block010_data_flat124 = (CoefficientMerge.fastMerge block010_data_flat122 block010_data_flat123) := by decide +kernel
theorem block010_data_flat124_original : block010_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)) := by
  rw [block010_data_flat124_step, block010_data_flat122_original, block010_data_flat123_original]
def block010_data_flat125 : CoefficientMerge.Poly := [(nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880))]
theorem block010_data_flat125_step : block010_data_flat125 = (CoefficientMerge.fastMerge block010_data_flat121 block010_data_flat124) := by decide +kernel
theorem block010_data_flat125_original : block010_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded))) := by
  rw [block010_data_flat125_step, block010_data_flat121_original, block010_data_flat124_original]
def block010_data_flat126 : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880))]
theorem block010_data_flat126_step : block010_data_flat126 = (CoefficientMerge.fastMerge block010_data_flat120 block010_data_flat125) := by decide +kernel
theorem block010_data_flat126_original : block010_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) := by
  rw [block010_data_flat126_step, block010_data_flat120_original, block010_data_flat125_original]
def block010_data_flat127 : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 164555278414560))]
theorem block010_data_flat127_step : block010_data_flat127 = (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) := by decide +kernel
theorem block010_data_flat127_original : block010_data_flat127 = (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) := by
  rw [block010_data_flat127_step]
def block010_data_flat128 : CoefficientMerge.Poly := [(nat_lit 827, Int.ofNat (nat_lit 316431248712480))]
theorem block010_data_flat128_step : block010_data_flat128 = (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded) := by decide +kernel
theorem block010_data_flat128_original : block010_data_flat128 = (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded) := by
  rw [block010_data_flat128_step]
def block010_data_flat129 : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480))]
theorem block010_data_flat129_step : block010_data_flat129 = (CoefficientMerge.fastMerge block010_data_flat127 block010_data_flat128) := by decide +kernel
theorem block010_data_flat129_original : block010_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) := by
  rw [block010_data_flat129_step, block010_data_flat127_original, block010_data_flat128_original]
def block010_data_flat130 : CoefficientMerge.Poly := [(nat_lit 828, Int.ofNat (nat_lit 322461649501200))]
theorem block010_data_flat130_step : block010_data_flat130 = (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) := by decide +kernel
theorem block010_data_flat130_original : block010_data_flat130 = (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) := by
  rw [block010_data_flat130_step]
def block010_data_flat131 : CoefficientMerge.Poly := [(nat_lit 829, Int.ofNat (nat_lit 304203431906352))]
theorem block010_data_flat131_step : block010_data_flat131 = (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) := by decide +kernel
theorem block010_data_flat131_original : block010_data_flat131 = (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) := by
  rw [block010_data_flat131_step]
def block010_data_flat132 : CoefficientMerge.Poly := [(nat_lit 830, Int.ofNat (nat_lit 282670457181552))]
theorem block010_data_flat132_step : block010_data_flat132 = (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded) := by decide +kernel
theorem block010_data_flat132_original : block010_data_flat132 = (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded) := by
  rw [block010_data_flat132_step]
def block010_data_flat133 : CoefficientMerge.Poly := [(nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552))]
theorem block010_data_flat133_step : block010_data_flat133 = (CoefficientMerge.fastMerge block010_data_flat131 block010_data_flat132) := by decide +kernel
theorem block010_data_flat133_original : block010_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded)) := by
  rw [block010_data_flat133_step, block010_data_flat131_original, block010_data_flat132_original]
def block010_data_flat134 : CoefficientMerge.Poly := [(nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552))]
theorem block010_data_flat134_step : block010_data_flat134 = (CoefficientMerge.fastMerge block010_data_flat130 block010_data_flat133) := by decide +kernel
theorem block010_data_flat134_original : block010_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))) := by
  rw [block010_data_flat134_step, block010_data_flat130_original, block010_data_flat133_original]
def block010_data_flat135 : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552))]
theorem block010_data_flat135_step : block010_data_flat135 = (CoefficientMerge.fastMerge block010_data_flat129 block010_data_flat134) := by decide +kernel
theorem block010_data_flat135_original : block010_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded)))) := by
  rw [block010_data_flat135_step, block010_data_flat129_original, block010_data_flat134_original]
def block010_data_flat136 : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552))]
theorem block010_data_flat136_step : block010_data_flat136 = (CoefficientMerge.fastMerge block010_data_flat126 block010_data_flat135) := by decide +kernel
theorem block010_data_flat136_original : block010_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) := by
  rw [block010_data_flat136_step, block010_data_flat126_original, block010_data_flat135_original]
def block010_data_flat137 : CoefficientMerge.Poly := [(nat_lit 831, Int.ofNat (nat_lit 283317992349552))]
theorem block010_data_flat137_step : block010_data_flat137 = (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) := by decide +kernel
theorem block010_data_flat137_original : block010_data_flat137 = (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) := by
  rw [block010_data_flat137_step]
def block010_data_flat138 : CoefficientMerge.Poly := [(nat_lit 832, Int.ofNat (nat_lit 266231762147952))]
theorem block010_data_flat138_step : block010_data_flat138 = (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded) := by decide +kernel
theorem block010_data_flat138_original : block010_data_flat138 = (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded) := by
  rw [block010_data_flat138_step]
def block010_data_flat139 : CoefficientMerge.Poly := [(nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952))]
theorem block010_data_flat139_step : block010_data_flat139 = (CoefficientMerge.fastMerge block010_data_flat137 block010_data_flat138) := by decide +kernel
theorem block010_data_flat139_original : block010_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) := by
  rw [block010_data_flat139_step, block010_data_flat137_original, block010_data_flat138_original]
def block010_data_flat140 : CoefficientMerge.Poly := [(nat_lit 833, Int.ofNat (nat_lit 264044639632752))]
theorem block010_data_flat140_step : block010_data_flat140 = (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) := by decide +kernel
theorem block010_data_flat140_original : block010_data_flat140 = (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) := by
  rw [block010_data_flat140_step]
def block010_data_flat141 : CoefficientMerge.Poly := [(nat_lit 834, Int.ofNat (nat_lit 313809511246704))]
theorem block010_data_flat141_step : block010_data_flat141 = (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) := by decide +kernel
theorem block010_data_flat141_original : block010_data_flat141 = (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) := by
  rw [block010_data_flat141_step]
def block010_data_flat142 : CoefficientMerge.Poly := [(nat_lit 835, Int.ofNat (nat_lit 287349206660208))]
theorem block010_data_flat142_step : block010_data_flat142 = (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded) := by decide +kernel
theorem block010_data_flat142_original : block010_data_flat142 = (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded) := by
  rw [block010_data_flat142_step]
def block010_data_flat143 : CoefficientMerge.Poly := [(nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208))]
theorem block010_data_flat143_step : block010_data_flat143 = (CoefficientMerge.fastMerge block010_data_flat141 block010_data_flat142) := by decide +kernel
theorem block010_data_flat143_original : block010_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)) := by
  rw [block010_data_flat143_step, block010_data_flat141_original, block010_data_flat142_original]
def block010_data_flat144 : CoefficientMerge.Poly := [(nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208))]
theorem block010_data_flat144_step : block010_data_flat144 = (CoefficientMerge.fastMerge block010_data_flat140 block010_data_flat143) := by decide +kernel
theorem block010_data_flat144_original : block010_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded))) := by
  rw [block010_data_flat144_step, block010_data_flat140_original, block010_data_flat143_original]
def block010_data_flat145 : CoefficientMerge.Poly := [(nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208))]
theorem block010_data_flat145_step : block010_data_flat145 = (CoefficientMerge.fastMerge block010_data_flat139 block010_data_flat144) := by decide +kernel
theorem block010_data_flat145_original : block010_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) := by
  rw [block010_data_flat145_step, block010_data_flat139_original, block010_data_flat144_original]
def block010_data_flat146 : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 337773555334512))]
theorem block010_data_flat146_step : block010_data_flat146 = (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) := by decide +kernel
theorem block010_data_flat146_original : block010_data_flat146 = (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) := by
  rw [block010_data_flat146_step]
def block010_data_flat147 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 333922903467120))]
theorem block010_data_flat147_step : block010_data_flat147 = (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded) := by decide +kernel
theorem block010_data_flat147_original : block010_data_flat147 = (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded) := by
  rw [block010_data_flat147_step]
def block010_data_flat148 : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120))]
theorem block010_data_flat148_step : block010_data_flat148 = (CoefficientMerge.fastMerge block010_data_flat146 block010_data_flat147) := by decide +kernel
theorem block010_data_flat148_original : block010_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) := by
  rw [block010_data_flat148_step, block010_data_flat146_original, block010_data_flat147_original]
def block010_data_flat149 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 349580333168640))]
theorem block010_data_flat149_step : block010_data_flat149 = (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) := by decide +kernel
theorem block010_data_flat149_original : block010_data_flat149 = (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) := by
  rw [block010_data_flat149_step]
def block010_data_flat150 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 338789442631680))]
theorem block010_data_flat150_step : block010_data_flat150 = (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) := by decide +kernel
theorem block010_data_flat150_original : block010_data_flat150 = (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) := by
  rw [block010_data_flat150_step]
def block010_data_flat151 : CoefficientMerge.Poly := [(nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat151_step : block010_data_flat151 = (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded) := by decide +kernel
theorem block010_data_flat151_original : block010_data_flat151 = (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded) := by
  rw [block010_data_flat151_step]
def block010_data_flat152 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat152_step : block010_data_flat152 = (CoefficientMerge.fastMerge block010_data_flat150 block010_data_flat151) := by decide +kernel
theorem block010_data_flat152_original : block010_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded)) := by
  rw [block010_data_flat152_step, block010_data_flat150_original, block010_data_flat151_original]
def block010_data_flat153 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat153_step : block010_data_flat153 = (CoefficientMerge.fastMerge block010_data_flat149 block010_data_flat152) := by decide +kernel
theorem block010_data_flat153_original : block010_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded))) := by
  rw [block010_data_flat153_step, block010_data_flat149_original, block010_data_flat152_original]
def block010_data_flat154 : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat154_step : block010_data_flat154 = (CoefficientMerge.fastMerge block010_data_flat148 block010_data_flat153) := by decide +kernel
theorem block010_data_flat154_original : block010_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded)))) := by
  rw [block010_data_flat154_step, block010_data_flat148_original, block010_data_flat153_original]
def block010_data_flat155 : CoefficientMerge.Poly := [(nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat155_step : block010_data_flat155 = (CoefficientMerge.fastMerge block010_data_flat145 block010_data_flat154) := by decide +kernel
theorem block010_data_flat155_original : block010_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded))))) := by
  rw [block010_data_flat155_step, block010_data_flat145_original, block010_data_flat154_original]
def block010_data_flat156 : CoefficientMerge.Poly := [(nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552)), (nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat156_step : block010_data_flat156 = (CoefficientMerge.fastMerge block010_data_flat136 block010_data_flat155) := by decide +kernel
theorem block010_data_flat156_original : block010_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded)))))) := by
  rw [block010_data_flat156_step, block010_data_flat136_original, block010_data_flat155_original]
def block010_data_flat157 : CoefficientMerge.Poly := [(nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800)), (nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984)), (nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552)), (nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat157_step : block010_data_flat157 = (CoefficientMerge.fastMerge block010_data_flat117 block010_data_flat156) := by decide +kernel
theorem block010_data_flat157_original : block010_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded))))))) := by
  rw [block010_data_flat157_step, block010_data_flat117_original, block010_data_flat156_original]
def block010_data_flat158 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400)), (nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720)), (nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000)), (nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200)), (nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800)), (nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984)), (nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552)), (nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat158_step : block010_data_flat158 = (CoefficientMerge.fastMerge block010_data_flat078 block010_data_flat157) := by decide +kernel
theorem block010_data_flat158_original : block010_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded)))))))) := by
  rw [block010_data_flat158_step, block010_data_flat078_original, block010_data_flat157_original]
def block010_data_flat159 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 142598777207040)), (nat_lit 728, Int.ofNat (nat_lit 121344224601600)), (nat_lit 729, Int.ofNat (nat_lit 129213729335592)), (nat_lit 730, Int.ofNat (nat_lit 156989643019704)), (nat_lit 731, Int.ofNat (nat_lit 178123796942256)), (nat_lit 732, Int.ofNat (nat_lit 218964915186336)), (nat_lit 733, Int.ofNat (nat_lit 205962588216000)), (nat_lit 734, Int.ofNat (nat_lit 187448867020800)), (nat_lit 735, Int.ofNat (nat_lit 191115655718400)), (nat_lit 736, Int.ofNat (nat_lit 177048679046400)), (nat_lit 737, Int.ofNat (nat_lit 177880810060800)), (nat_lit 738, Int.ofNat (nat_lit 227305139846400)), (nat_lit 739, Int.ofNat (nat_lit 197144498073600)), (nat_lit 740, Int.ofNat (nat_lit 243868509561600)), (nat_lit 741, Int.ofNat (nat_lit 229597929792000)), (nat_lit 742, Int.ofNat (nat_lit 292791670752000)), (nat_lit 743, Int.ofNat (nat_lit 280178158176000)), (nat_lit 751, Int.ofNat (nat_lit 97409907302400)), (nat_lit 752, Int.ofNat (nat_lit 166327558467840)), (nat_lit 753, Int.ofNat (nat_lit 145263690951720)), (nat_lit 754, Int.ofNat (nat_lit 170879862994104)), (nat_lit 755, Int.ofNat (nat_lit 193055872007856)), (nat_lit 756, Int.ofNat (nat_lit 234938845343136)), (nat_lit 757, Int.ofNat (nat_lit 221947149547200)), (nat_lit 758, Int.ofNat (nat_lit 203444059526400)), (nat_lit 759, Int.ofNat (nat_lit 207121479398400)), (nat_lit 760, Int.ofNat (nat_lit 193065133900800)), (nat_lit 761, Int.ofNat (nat_lit 193907896089600)), (nat_lit 762, Int.ofNat (nat_lit 244507561267200)), (nat_lit 763, Int.ofNat (nat_lit 216686959104000)), (nat_lit 764, Int.ofNat (nat_lit 265751010201600)), (nat_lit 765, Int.ofNat (nat_lit 256149878476800)), (nat_lit 766, Int.ofNat (nat_lit 326703148352000)), (nat_lit 767, Int.ofNat (nat_lit 316265679676800)), (nat_lit 776, Int.ofNat (nat_lit 113923664870400)), (nat_lit 777, Int.ofNat (nat_lit 204854516840160)), (nat_lit 778, Int.ofNat (nat_lit 188840203618968)), (nat_lit 779, Int.ofNat (nat_lit 207125640705456)), (nat_lit 780, Int.ofNat (nat_lit 246967428555936)), (nat_lit 781, Int.ofNat (nat_lit 233476067563200)), (nat_lit 782, Int.ofNat (nat_lit 214473312345600)), (nat_lit 783, Int.ofNat (nat_lit 217651067020800)), (nat_lit 784, Int.ofNat (nat_lit 203095056326400)), (nat_lit 785, Int.ofNat (nat_lit 203438153318400)), (nat_lit 786, Int.ofNat (nat_lit 255265128518400)), (nat_lit 787, Int.ofNat (nat_lit 230398811596800)), (nat_lit 788, Int.ofNat (nat_lit 282417147936000)), (nat_lit 789, Int.ofNat (nat_lit 279224251891200)), (nat_lit 790, Int.ofNat (nat_lit 356557454803200)), (nat_lit 791, Int.ofNat (nat_lit 349745019724800)), (nat_lit 801, Int.ofNat (nat_lit 136999274369760)), (nat_lit 802, Int.ofNat (nat_lit 255486130384320)), (nat_lit 803, Int.ofNat (nat_lit 242659403316000)), (nat_lit 804, Int.ofNat (nat_lit 272104064602128)), (nat_lit 805, Int.ofNat (nat_lit 256061221753392)), (nat_lit 806, Int.ofNat (nat_lit 236048504967792)), (nat_lit 807, Int.ofNat (nat_lit 238216298074992)), (nat_lit 808, Int.ofNat (nat_lit 222650325812592)), (nat_lit 809, Int.ofNat (nat_lit 221983461236592)), (nat_lit 810, Int.ofNat (nat_lit 273902208783984)), (nat_lit 811, Int.ofNat (nat_lit 250229398125168)), (nat_lit 812, Int.ofNat (nat_lit 303441240727152)), (nat_lit 813, Int.ofNat (nat_lit 303645318775920)), (nat_lit 814, Int.ofNat (nat_lit 368500279875840)), (nat_lit 815, Int.ofNat (nat_lit 362803493738880)), (nat_lit 826, Int.ofNat (nat_lit 164555278414560)), (nat_lit 827, Int.ofNat (nat_lit 316431248712480)), (nat_lit 828, Int.ofNat (nat_lit 322461649501200)), (nat_lit 829, Int.ofNat (nat_lit 304203431906352)), (nat_lit 830, Int.ofNat (nat_lit 282670457181552)), (nat_lit 831, Int.ofNat (nat_lit 283317992349552)), (nat_lit 832, Int.ofNat (nat_lit 266231762147952)), (nat_lit 833, Int.ofNat (nat_lit 264044639632752)), (nat_lit 834, Int.ofNat (nat_lit 313809511246704)), (nat_lit 835, Int.ofNat (nat_lit 287349206660208)), (nat_lit 836, Int.ofNat (nat_lit 337773555334512)), (nat_lit 837, Int.ofNat (nat_lit 333922903467120)), (nat_lit 838, Int.ofNat (nat_lit 349580333168640)), (nat_lit 839, Int.ofNat (nat_lit 338789442631680)), (nat_lit 851, Int.ofNat (nat_lit 201506544866880))]
theorem block010_data_flat159_step : block010_data_flat159 = (CoefficientMerge.trim block010_data_flat158) := by decide +kernel
theorem block010_data_flat159_original : block010_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded))))))))) := by
  rw [block010_data_flat159_step, block010_data_flat158_original]
theorem block010_data : block010 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142598777207040 : Int) atom0609Coded) (CoefficientMerge.scale (121344224601600 : Int) atom0610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129213729335592 : Int) atom0611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156989643019704 : Int) atom0612Coded) (CoefficientMerge.scale (178123796942256 : Int) atom0613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218964915186336 : Int) atom0614Coded) (CoefficientMerge.scale (205962588216000 : Int) atom0615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187448867020800 : Int) atom0616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191115655718400 : Int) atom0617Coded) (CoefficientMerge.scale (177048679046400 : Int) atom0618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177880810060800 : Int) atom0619Coded) (CoefficientMerge.scale (227305139846400 : Int) atom0620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197144498073600 : Int) atom0621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243868509561600 : Int) atom0622Coded) (CoefficientMerge.scale (229597929792000 : Int) atom0623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (292791670752000 : Int) atom0624Coded) (CoefficientMerge.scale (280178158176000 : Int) atom0625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97409907302400 : Int) atom0626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (166327558467840 : Int) atom0627Coded) (CoefficientMerge.scale (145263690951720 : Int) atom0628Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (170879862994104 : Int) atom0629Coded) (CoefficientMerge.scale (193055872007856 : Int) atom0630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (234938845343136 : Int) atom0631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221947149547200 : Int) atom0632Coded) (CoefficientMerge.scale (203444059526400 : Int) atom0633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207121479398400 : Int) atom0634Coded) (CoefficientMerge.scale (193065133900800 : Int) atom0635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193907896089600 : Int) atom0636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244507561267200 : Int) atom0637Coded) (CoefficientMerge.scale (216686959104000 : Int) atom0638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265751010201600 : Int) atom0639Coded) (CoefficientMerge.scale (256149878476800 : Int) atom0640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (326703148352000 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316265679676800 : Int) atom0642Coded) (CoefficientMerge.scale (113923664870400 : Int) atom0643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204854516840160 : Int) atom0644Coded) (CoefficientMerge.scale (188840203618968 : Int) atom0645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207125640705456 : Int) atom0646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246967428555936 : Int) atom0647Coded) (CoefficientMerge.scale (233476067563200 : Int) atom0648Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (214473312345600 : Int) atom0649Coded) (CoefficientMerge.scale (217651067020800 : Int) atom0650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203095056326400 : Int) atom0651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203438153318400 : Int) atom0652Coded) (CoefficientMerge.scale (255265128518400 : Int) atom0653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230398811596800 : Int) atom0654Coded) (CoefficientMerge.scale (282417147936000 : Int) atom0655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (279224251891200 : Int) atom0656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356557454803200 : Int) atom0657Coded) (CoefficientMerge.scale (349745019724800 : Int) atom0658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (136999274369760 : Int) atom0659Coded) (CoefficientMerge.scale (255486130384320 : Int) atom0660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242659403316000 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272104064602128 : Int) atom0662Coded) (CoefficientMerge.scale (256061221753392 : Int) atom0663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236048504967792 : Int) atom0664Coded) (CoefficientMerge.scale (238216298074992 : Int) atom0665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222650325812592 : Int) atom0666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221983461236592 : Int) atom0667Coded) (CoefficientMerge.scale (273902208783984 : Int) atom0668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250229398125168 : Int) atom0669Coded) (CoefficientMerge.scale (303441240727152 : Int) atom0670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303645318775920 : Int) atom0671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368500279875840 : Int) atom0672Coded) (CoefficientMerge.scale (362803493738880 : Int) atom0673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164555278414560 : Int) atom0674Coded) (CoefficientMerge.scale (316431248712480 : Int) atom0675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (322461649501200 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304203431906352 : Int) atom0677Coded) (CoefficientMerge.scale (282670457181552 : Int) atom0678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283317992349552 : Int) atom0679Coded) (CoefficientMerge.scale (266231762147952 : Int) atom0680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264044639632752 : Int) atom0681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (313809511246704 : Int) atom0682Coded) (CoefficientMerge.scale (287349206660208 : Int) atom0683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337773555334512 : Int) atom0684Coded) (CoefficientMerge.scale (333922903467120 : Int) atom0685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349580333168640 : Int) atom0686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338789442631680 : Int) atom0687Coded) (CoefficientMerge.scale (201506544866880 : Int) atom0688Coded)))))))) := by
  have h : block010 = block010_data_flat159 := by decide +kernel
  exact h.trans block010_data_flat159_original
theorem block010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block010 := by
  rw [block010_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0609Coded_nonneg g hg hA hB) (atom0610Coded_nonneg g hg hA hB)) (add_nonneg (atom0611Coded_nonneg g hg hA hB) (add_nonneg (atom0612Coded_nonneg g hg hA hB) (atom0613Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0614Coded_nonneg g hg hA hB) (atom0615Coded_nonneg g hg hA hB)) (add_nonneg (atom0616Coded_nonneg g hg hA hB) (add_nonneg (atom0617Coded_nonneg g hg hA hB) (atom0618Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0619Coded_nonneg g hg hA hB) (atom0620Coded_nonneg g hg hA hB)) (add_nonneg (atom0621Coded_nonneg g hg hA hB) (add_nonneg (atom0622Coded_nonneg g hg hA hB) (atom0623Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0624Coded_nonneg g hg hA hB) (atom0625Coded_nonneg g hg hA hB)) (add_nonneg (atom0626Coded_nonneg g hg hA hB) (add_nonneg (atom0627Coded_nonneg g hg hA hB) (atom0628Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0629Coded_nonneg g hg hA hB) (atom0630Coded_nonneg g hg hA hB)) (add_nonneg (atom0631Coded_nonneg g hg hA hB) (add_nonneg (atom0632Coded_nonneg g hg hA hB) (atom0633Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0634Coded_nonneg g hg hA hB) (atom0635Coded_nonneg g hg hA hB)) (add_nonneg (atom0636Coded_nonneg g hg hA hB) (add_nonneg (atom0637Coded_nonneg g hg hA hB) (atom0638Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0639Coded_nonneg g hg hA hB) (atom0640Coded_nonneg g hg hA hB)) (add_nonneg (atom0641Coded_nonneg g hg hA hB) (add_nonneg (atom0642Coded_nonneg g hg hA hB) (atom0643Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0644Coded_nonneg g hg hA hB) (atom0645Coded_nonneg g hg hA hB)) (add_nonneg (atom0646Coded_nonneg g hg hA hB) (add_nonneg (atom0647Coded_nonneg g hg hA hB) (atom0648Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0649Coded_nonneg g hg hA hB) (atom0650Coded_nonneg g hg hA hB)) (add_nonneg (atom0651Coded_nonneg g hg hA hB) (add_nonneg (atom0652Coded_nonneg g hg hA hB) (atom0653Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0654Coded_nonneg g hg hA hB) (atom0655Coded_nonneg g hg hA hB)) (add_nonneg (atom0656Coded_nonneg g hg hA hB) (add_nonneg (atom0657Coded_nonneg g hg hA hB) (atom0658Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0659Coded_nonneg g hg hA hB) (atom0660Coded_nonneg g hg hA hB)) (add_nonneg (atom0661Coded_nonneg g hg hA hB) (add_nonneg (atom0662Coded_nonneg g hg hA hB) (atom0663Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0664Coded_nonneg g hg hA hB) (atom0665Coded_nonneg g hg hA hB)) (add_nonneg (atom0666Coded_nonneg g hg hA hB) (add_nonneg (atom0667Coded_nonneg g hg hA hB) (atom0668Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0669Coded_nonneg g hg hA hB) (atom0670Coded_nonneg g hg hA hB)) (add_nonneg (atom0671Coded_nonneg g hg hA hB) (add_nonneg (atom0672Coded_nonneg g hg hA hB) (atom0673Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0674Coded_nonneg g hg hA hB) (atom0675Coded_nonneg g hg hA hB)) (add_nonneg (atom0676Coded_nonneg g hg hA hB) (add_nonneg (atom0677Coded_nonneg g hg hA hB) (atom0678Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0679Coded_nonneg g hg hA hB) (atom0680Coded_nonneg g hg hA hB)) (add_nonneg (atom0681Coded_nonneg g hg hA hB) (add_nonneg (atom0682Coded_nonneg g hg hA hB) (atom0683Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0684Coded_nonneg g hg hA hB) (atom0685Coded_nonneg g hg hA hB)) (add_nonneg (atom0686Coded_nonneg g hg hA hB) (add_nonneg (atom0687Coded_nonneg g hg hA hB) (atom0688Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
