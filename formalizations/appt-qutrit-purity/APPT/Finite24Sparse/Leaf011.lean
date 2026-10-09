import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0689 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0689 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0689 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0689_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (394708547851200 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0689Coded : CoefficientMerge.Poly := [(nat_lit 852, Int.ofNat (nat_lit 1))]
theorem atom0689Coded_decode : atom0689 = SparsePolynomial.decodeCubic 24 atom0689Coded := by decide +kernel
theorem atom0689Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (394708547851200 : Int) atom0689Coded) := by
  have h := atom0689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0690 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0690 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0690 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0690_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353450265078240 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690Coded : CoefficientMerge.Poly := [(nat_lit 853, Int.ofNat (nat_lit 1))]
theorem atom0690Coded_decode : atom0690 = SparsePolynomial.decodeCubic 24 atom0690Coded := by decide +kernel
theorem atom0690Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (353450265078240 : Int) atom0690Coded) := by
  have h := atom0690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0691 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0691 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0691 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0691_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321640443169056 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691Coded : CoefficientMerge.Poly := [(nat_lit 854, Int.ofNat (nat_lit 1))]
theorem atom0691Coded_decode : atom0691 = SparsePolynomial.decodeCubic 24 atom0691Coded := by decide +kernel
theorem atom0691Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321640443169056 : Int) atom0691Coded) := by
  have h := atom0691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0692 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0692 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0692 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0692_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318715903738656 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692Coded : CoefficientMerge.Poly := [(nat_lit 855, Int.ofNat (nat_lit 1))]
theorem atom0692Coded_decode : atom0692 = SparsePolynomial.decodeCubic 24 atom0692Coded := by decide +kernel
theorem atom0692Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (318715903738656 : Int) atom0692Coded) := by
  have h := atom0692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0693 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0693 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0693 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0693_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299599119226656 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693Coded : CoefficientMerge.Poly := [(nat_lit 856, Int.ofNat (nat_lit 1))]
theorem atom0693Coded_decode : atom0693 = SparsePolynomial.decodeCubic 24 atom0693Coded := by decide +kernel
theorem atom0693Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299599119226656 : Int) atom0693Coded) := by
  have h := atom0693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0694 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0694 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0694 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0694_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (295381442401056 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694Coded : CoefficientMerge.Poly := [(nat_lit 857, Int.ofNat (nat_lit 1))]
theorem atom0694Coded_decode : atom0694 = SparsePolynomial.decodeCubic 24 atom0694Coded := by decide +kernel
theorem atom0694Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (295381442401056 : Int) atom0694Coded) := by
  have h := atom0694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0695 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0695 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0695 = ((g 1) * (g 11) * (g 18)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0695_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349182426719808 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695Coded : CoefficientMerge.Poly := [(nat_lit 858, Int.ofNat (nat_lit 1))]
theorem atom0695Coded_decode : atom0695 = SparsePolynomial.decodeCubic 24 atom0695Coded := by decide +kernel
theorem atom0695Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349182426719808 : Int) atom0695Coded) := by
  have h := atom0695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0696 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0696 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0696 = ((g 1) * (g 11) * (g 19)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0696_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315381779675424 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696Coded : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 1))]
theorem atom0696Coded_decode : atom0696 = SparsePolynomial.decodeCubic 24 atom0696Coded := by decide +kernel
theorem atom0696Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315381779675424 : Int) atom0696Coded) := by
  have h := atom0696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0697 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0697 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0697 = ((g 1) * (g 11) * (g 20)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0697_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369424182777408 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697Coded : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 1))]
theorem atom0697Coded_decode : atom0697 = SparsePolynomial.decodeCubic 24 atom0697Coded := by decide +kernel
theorem atom0697Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (369424182777408 : Int) atom0697Coded) := by
  have h := atom0697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0698 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0698 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0698 = ((g 1) * (g 11) * (g 21)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0698_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (359408125596960 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698Coded : CoefficientMerge.Poly := [(nat_lit 861, Int.ofNat (nat_lit 1))]
theorem atom0698Coded_decode : atom0698 = SparsePolynomial.decodeCubic 24 atom0698Coded := by decide +kernel
theorem atom0698Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (359408125596960 : Int) atom0698Coded) := by
  have h := atom0698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0699 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0699 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0699 = ((g 1) * (g 11) * (g 22)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0699_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330379014712320 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699Coded : CoefficientMerge.Poly := [(nat_lit 862, Int.ofNat (nat_lit 1))]
theorem atom0699Coded_decode : atom0699 = SparsePolynomial.decodeCubic 24 atom0699Coded := by decide +kernel
theorem atom0699Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (330379014712320 : Int) atom0699Coded) := by
  have h := atom0699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0700 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0700 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0700 = ((g 1) * (g 11) * (g 23)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0700_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338126709026304 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700Coded : CoefficientMerge.Poly := [(nat_lit 863, Int.ofNat (nat_lit 1))]
theorem atom0700Coded_decode : atom0700 = SparsePolynomial.decodeCubic 24 atom0700Coded := by decide +kernel
theorem atom0700Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338126709026304 : Int) atom0700Coded) := by
  have h := atom0700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0701 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0701 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0701 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0701_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242832577553280 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701Coded : CoefficientMerge.Poly := [(nat_lit 876, Int.ofNat (nat_lit 1))]
theorem atom0701Coded_decode : atom0701 = SparsePolynomial.decodeCubic 24 atom0701Coded := by decide +kernel
theorem atom0701Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242832577553280 : Int) atom0701Coded) := by
  have h := atom0701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0702 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0702 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0702 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0702_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (435085192840320 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702Coded : CoefficientMerge.Poly := [(nat_lit 877, Int.ofNat (nat_lit 1))]
theorem atom0702Coded_decode : atom0702 = SparsePolynomial.decodeCubic 24 atom0702Coded := by decide +kernel
theorem atom0702Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (435085192840320 : Int) atom0702Coded) := by
  have h := atom0702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0703 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0703 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0703 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0703_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (385560346343040 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703Coded : CoefficientMerge.Poly := [(nat_lit 878, Int.ofNat (nat_lit 1))]
theorem atom0703Coded_decode : atom0703 = SparsePolynomial.decodeCubic 24 atom0703Coded := by decide +kernel
theorem atom0703Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (385560346343040 : Int) atom0703Coded) := by
  have h := atom0703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0704 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0704 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0704 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0704_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379386155583936 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704Coded : CoefficientMerge.Poly := [(nat_lit 879, Int.ofNat (nat_lit 1))]
theorem atom0704Coded_decode : atom0704 = SparsePolynomial.decodeCubic 24 atom0704Coded := by decide +kernel
theorem atom0704Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379386155583936 : Int) atom0704Coded) := by
  have h := atom0704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0705 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0705 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0705 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0705_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (357728520390336 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705Coded : CoefficientMerge.Poly := [(nat_lit 880, Int.ofNat (nat_lit 1))]
theorem atom0705Coded_decode : atom0705 = SparsePolynomial.decodeCubic 24 atom0705Coded := by decide +kernel
theorem atom0705Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (357728520390336 : Int) atom0705Coded) := by
  have h := atom0705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0706 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0706 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0706 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0706_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350969992883136 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706Coded : CoefficientMerge.Poly := [(nat_lit 881, Int.ofNat (nat_lit 1))]
theorem atom0706Coded_decode : atom0706 = SparsePolynomial.decodeCubic 24 atom0706Coded := by decide +kernel
theorem atom0706Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350969992883136 : Int) atom0706Coded) := by
  have h := atom0706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0707 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0707 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0707 = ((g 1) * (g 12) * (g 18)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0707_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415062219800448 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707Coded : CoefficientMerge.Poly := [(nat_lit 882, Int.ofNat (nat_lit 1))]
theorem atom0707Coded_decode : atom0707 = SparsePolynomial.decodeCubic 24 atom0707Coded := by decide +kernel
theorem atom0707Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415062219800448 : Int) atom0707Coded) := by
  have h := atom0707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0708 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0708 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0708 = ((g 1) * (g 12) * (g 19)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0708_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361270446634944 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708Coded : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 1))]
theorem atom0708Coded_decode : atom0708 = SparsePolynomial.decodeCubic 24 atom0708Coded := by decide +kernel
theorem atom0708Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (361270446634944 : Int) atom0708Coded) := by
  have h := atom0708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0709 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0709 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0709 = ((g 1) * (g 12) * (g 20)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0709_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439386346827648 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709Coded : CoefficientMerge.Poly := [(nat_lit 884, Int.ofNat (nat_lit 1))]
theorem atom0709Coded_decode : atom0709 = SparsePolynomial.decodeCubic 24 atom0709Coded := by decide +kernel
theorem atom0709Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439386346827648 : Int) atom0709Coded) := by
  have h := atom0709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0710 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0710 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0710 = ((g 1) * (g 12) * (g 21)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0710_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390978726874560 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710Coded : CoefficientMerge.Poly := [(nat_lit 885, Int.ofNat (nat_lit 1))]
theorem atom0710Coded_decode : atom0710 = SparsePolynomial.decodeCubic 24 atom0710Coded := by decide +kernel
theorem atom0710Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (390978726874560 : Int) atom0710Coded) := by
  have h := atom0710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0711 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0711 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0711 = ((g 1) * (g 12) * (g 22)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0711_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (325176814433280 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711Coded : CoefficientMerge.Poly := [(nat_lit 886, Int.ofNat (nat_lit 1))]
theorem atom0711Coded_decode : atom0711 = SparsePolynomial.decodeCubic 24 atom0711Coded := by decide +kernel
theorem atom0711Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (325176814433280 : Int) atom0711Coded) := by
  have h := atom0711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0712 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0712 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0712 = ((g 1) * (g 12) * (g 23)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0712_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324378474292224 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712Coded : CoefficientMerge.Poly := [(nat_lit 887, Int.ofNat (nat_lit 1))]
theorem atom0712Coded_decode : atom0712 = SparsePolynomial.decodeCubic 24 atom0712Coded := by decide +kernel
theorem atom0712Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324378474292224 : Int) atom0712Coded) := by
  have h := atom0712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0713 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0713 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0713 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0713_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241883189856000 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713Coded : CoefficientMerge.Poly := [(nat_lit 901, Int.ofNat (nat_lit 1))]
theorem atom0713Coded_decode : atom0713 = SparsePolynomial.decodeCubic 24 atom0713Coded := by decide +kernel
theorem atom0713Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241883189856000 : Int) atom0713Coded) := by
  have h := atom0713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0714 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0714 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0714 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0714_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422611559979840 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714Coded : CoefficientMerge.Poly := [(nat_lit 902, Int.ofNat (nat_lit 1))]
theorem atom0714Coded_decode : atom0714 = SparsePolynomial.decodeCubic 24 atom0714Coded := by decide +kernel
theorem atom0714Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422611559979840 : Int) atom0714Coded) := by
  have h := atom0714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0715 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0715 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0715 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0715_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (385974487301760 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715Coded : CoefficientMerge.Poly := [(nat_lit 903, Int.ofNat (nat_lit 1))]
theorem atom0715Coded_decode : atom0715 = SparsePolynomial.decodeCubic 24 atom0715Coded := by decide +kernel
theorem atom0715Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (385974487301760 : Int) atom0715Coded) := by
  have h := atom0715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0716 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0716 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0716 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0716_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358553364624000 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716Coded : CoefficientMerge.Poly := [(nat_lit 904, Int.ofNat (nat_lit 1))]
theorem atom0716Coded_decode : atom0716 = SparsePolynomial.decodeCubic 24 atom0716Coded := by decide +kernel
theorem atom0716Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358553364624000 : Int) atom0716Coded) := by
  have h := atom0716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0717 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0717 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0717 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0717_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (348743690064000 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717Coded : CoefficientMerge.Poly := [(nat_lit 905, Int.ofNat (nat_lit 1))]
theorem atom0717Coded_decode : atom0717 = SparsePolynomial.decodeCubic 24 atom0717Coded := by decide +kernel
theorem atom0717Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (348743690064000 : Int) atom0717Coded) := by
  have h := atom0717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0718 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0718 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0718 = ((g 1) * (g 13) * (g 18)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0718_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407775787372800 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718Coded : CoefficientMerge.Poly := [(nat_lit 906, Int.ofNat (nat_lit 1))]
theorem atom0718Coded_decode : atom0718 = SparsePolynomial.decodeCubic 24 atom0718Coded := by decide +kernel
theorem atom0718Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (407775787372800 : Int) atom0718Coded) := by
  have h := atom0718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0719 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0719 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0719 = ((g 1) * (g 13) * (g 19)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0719_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (355536072460800 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719Coded : CoefficientMerge.Poly := [(nat_lit 907, Int.ofNat (nat_lit 1))]
theorem atom0719Coded_decode : atom0719 = SparsePolynomial.decodeCubic 24 atom0719Coded := by decide +kernel
theorem atom0719Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (355536072460800 : Int) atom0719Coded) := by
  have h := atom0719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0720 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0720 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0720 = ((g 1) * (g 13) * (g 20)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0720_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436182285369600 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720Coded : CoefficientMerge.Poly := [(nat_lit 908, Int.ofNat (nat_lit 1))]
theorem atom0720Coded_decode : atom0720 = SparsePolynomial.decodeCubic 24 atom0720Coded := by decide +kernel
theorem atom0720Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (436182285369600 : Int) atom0720Coded) := by
  have h := atom0720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0721 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0721 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0721 = ((g 1) * (g 13) * (g 21)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0721_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (384330504096000 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721Coded : CoefficientMerge.Poly := [(nat_lit 909, Int.ofNat (nat_lit 1))]
theorem atom0721Coded_decode : atom0721 = SparsePolynomial.decodeCubic 24 atom0721Coded := by decide +kernel
theorem atom0721Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (384330504096000 : Int) atom0721Coded) := by
  have h := atom0721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0722 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0722 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0722 = ((g 1) * (g 13) * (g 22)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0722_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327597538800000 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722Coded : CoefficientMerge.Poly := [(nat_lit 910, Int.ofNat (nat_lit 1))]
theorem atom0722Coded_decode : atom0722 = SparsePolynomial.decodeCubic 24 atom0722Coded := by decide +kernel
theorem atom0722Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327597538800000 : Int) atom0722Coded) := by
  have h := atom0722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0723 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0723 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0723 = ((g 1) * (g 13) * (g 23)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0723_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327207015273600 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723Coded : CoefficientMerge.Poly := [(nat_lit 911, Int.ofNat (nat_lit 1))]
theorem atom0723Coded_decode : atom0723 = SparsePolynomial.decodeCubic 24 atom0723Coded := by decide +kernel
theorem atom0723Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327207015273600 : Int) atom0723Coded) := by
  have h := atom0723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0724 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0724 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0724 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0724_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230358944692800 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724Coded : CoefficientMerge.Poly := [(nat_lit 926, Int.ofNat (nat_lit 1))]
theorem atom0724Coded_decode : atom0724 = SparsePolynomial.decodeCubic 24 atom0724Coded := by decide +kernel
theorem atom0724Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230358944692800 : Int) atom0724Coded) := by
  have h := atom0724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0725 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0725 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0725 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0725_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415536541842240 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725Coded : CoefficientMerge.Poly := [(nat_lit 927, Int.ofNat (nat_lit 1))]
theorem atom0725Coded_decode : atom0725 = SparsePolynomial.decodeCubic 24 atom0725Coded := by decide +kernel
theorem atom0725Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415536541842240 : Int) atom0725Coded) := by
  have h := atom0725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0726 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0726 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0726 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0726_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358531991415360 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726Coded : CoefficientMerge.Poly := [(nat_lit 928, Int.ofNat (nat_lit 1))]
theorem atom0726Coded_decode : atom0726 = SparsePolynomial.decodeCubic 24 atom0726Coded := by decide +kernel
theorem atom0726Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358531991415360 : Int) atom0726Coded) := by
  have h := atom0726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0727 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0727 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0727 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0727_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344356141852800 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727Coded : CoefficientMerge.Poly := [(nat_lit 929, Int.ofNat (nat_lit 1))]
theorem atom0727Coded_decode : atom0727 = SparsePolynomial.decodeCubic 24 atom0727Coded := by decide +kernel
theorem atom0727Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344356141852800 : Int) atom0727Coded) := by
  have h := atom0727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0728 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0728 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0728 = ((g 1) * (g 14) * (g 18)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0728_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393140829312000 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728Coded : CoefficientMerge.Poly := [(nat_lit 930, Int.ofNat (nat_lit 1))]
theorem atom0728Coded_decode : atom0728 = SparsePolynomial.decodeCubic 24 atom0728Coded := by decide +kernel
theorem atom0728Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (393140829312000 : Int) atom0728Coded) := by
  have h := atom0728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0729 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0729 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0729 = ((g 1) * (g 14) * (g 19)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0729_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345302980822800 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729Coded : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 1))]
theorem atom0729Coded_decode : atom0729 = SparsePolynomial.decodeCubic 24 atom0729Coded := by decide +kernel
theorem atom0729Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345302980822800 : Int) atom0729Coded) := by
  have h := atom0729_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0729Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0730 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0730 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0730 = ((g 1) * (g 14) * (g 20)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0730_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425629698278400 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730Coded : CoefficientMerge.Poly := [(nat_lit 932, Int.ofNat (nat_lit 1))]
theorem atom0730Coded_decode : atom0730 = SparsePolynomial.decodeCubic 24 atom0730Coded := by decide +kernel
theorem atom0730Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (425629698278400 : Int) atom0730Coded) := by
  have h := atom0730_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0730Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0731 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0731 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0731 = ((g 1) * (g 14) * (g 21)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0731_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375819102489600 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731Coded : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 1))]
theorem atom0731Coded_decode : atom0731 = SparsePolynomial.decodeCubic 24 atom0731Coded := by decide +kernel
theorem atom0731Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375819102489600 : Int) atom0731Coded) := by
  have h := atom0731_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0731Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0732 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0732 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0732 = ((g 1) * (g 14) * (g 22)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0732_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323273321641200 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732Coded : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 1))]
theorem atom0732Coded_decode : atom0732 = SparsePolynomial.decodeCubic 24 atom0732Coded := by decide +kernel
theorem atom0732Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (323273321641200 : Int) atom0732Coded) := by
  have h := atom0732_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0732Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0733 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0733 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0733 = ((g 1) * (g 14) * (g 23)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0733_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321024479252400 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733Coded : CoefficientMerge.Poly := [(nat_lit 935, Int.ofNat (nat_lit 1))]
theorem atom0733Coded_decode : atom0733 = SparsePolynomial.decodeCubic 24 atom0733Coded := by decide +kernel
theorem atom0733Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321024479252400 : Int) atom0733Coded) := by
  have h := atom0733_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0733Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0734 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0734 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0734 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0734_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236349692006400 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734Coded : CoefficientMerge.Poly := [(nat_lit 951, Int.ofNat (nat_lit 1))]
theorem atom0734Coded_decode : atom0734 = SparsePolynomial.decodeCubic 24 atom0734Coded := by decide +kernel
theorem atom0734Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236349692006400 : Int) atom0734Coded) := by
  have h := atom0734_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0734Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0735 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0735 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0735 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0735_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402531313443840 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0735Coded : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 1))]
theorem atom0735Coded_decode : atom0735 = SparsePolynomial.decodeCubic 24 atom0735Coded := by decide +kernel
theorem atom0735Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402531313443840 : Int) atom0735Coded) := by
  have h := atom0735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0736 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0736 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (362157076915200 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736Coded : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 1))]
theorem atom0736Coded_decode : atom0736 = SparsePolynomial.decodeCubic 24 atom0736Coded := by decide +kernel
theorem atom0736Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (362157076915200 : Int) atom0736Coded) := by
  have h := atom0736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0737 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0737 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 1) * (g 15) * (g 18)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (408079884441600 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737Coded : CoefficientMerge.Poly := [(nat_lit 954, Int.ofNat (nat_lit 1))]
theorem atom0737Coded_decode : atom0737 = SparsePolynomial.decodeCubic 24 atom0737Coded := by decide +kernel
theorem atom0737Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (408079884441600 : Int) atom0737Coded) := by
  have h := atom0737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0738 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0738 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 1) * (g 15) * (g 19)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352712728166400 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738Coded : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 1))]
theorem atom0738Coded_decode : atom0738 = SparsePolynomial.decodeCubic 24 atom0738Coded := by decide +kernel
theorem atom0738Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352712728166400 : Int) atom0738Coded) := by
  have h := atom0738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0739 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0739 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 1) * (g 15) * (g 20)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444651124377600 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739Coded : CoefficientMerge.Poly := [(nat_lit 956, Int.ofNat (nat_lit 1))]
theorem atom0739Coded_decode : atom0739 = SparsePolynomial.decodeCubic 24 atom0739Coded := by decide +kernel
theorem atom0739Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (444651124377600 : Int) atom0739Coded) := by
  have h := atom0739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0740 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0740 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 1) * (g 15) * (g 21)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (396881714073600 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740Coded : CoefficientMerge.Poly := [(nat_lit 957, Int.ofNat (nat_lit 1))]
theorem atom0740Coded_decode : atom0740 = SparsePolynomial.decodeCubic 24 atom0740Coded := by decide +kernel
theorem atom0740Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (396881714073600 : Int) atom0740Coded) := by
  have h := atom0740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0741 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0741 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 1) * (g 15) * (g 22)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308523875923200 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741Coded : CoefficientMerge.Poly := [(nat_lit 958, Int.ofNat (nat_lit 1))]
theorem atom0741Coded_decode : atom0741 = SparsePolynomial.decodeCubic 24 atom0741Coded := by decide +kernel
theorem atom0741Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (308523875923200 : Int) atom0741Coded) := by
  have h := atom0741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0742 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0742 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 1) * (g 15) * (g 23)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (301811953766400 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742Coded : CoefficientMerge.Poly := [(nat_lit 959, Int.ofNat (nat_lit 1))]
theorem atom0742Coded_decode : atom0742 = SparsePolynomial.decodeCubic 24 atom0742Coded := by decide +kernel
theorem atom0742Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (301811953766400 : Int) atom0742Coded) := by
  have h := atom0742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0743 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0743 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218895236582400 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743Coded : CoefficientMerge.Poly := [(nat_lit 976, Int.ofNat (nat_lit 1))]
theorem atom0743Coded_decode : atom0743 = SparsePolynomial.decodeCubic 24 atom0743Coded := by decide +kernel
theorem atom0743Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218895236582400 : Int) atom0743Coded) := by
  have h := atom0743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0744 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0744 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (376667448729600 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744Coded : CoefficientMerge.Poly := [(nat_lit 977, Int.ofNat (nat_lit 1))]
theorem atom0744Coded_decode : atom0744 = SparsePolynomial.decodeCubic 24 atom0744Coded := by decide +kernel
theorem atom0744Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (376667448729600 : Int) atom0744Coded) := by
  have h := atom0744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0745 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0745 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 1) * (g 16) * (g 18)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399373919078400 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745Coded : CoefficientMerge.Poly := [(nat_lit 978, Int.ofNat (nat_lit 1))]
theorem atom0745Coded_decode : atom0745 = SparsePolynomial.decodeCubic 24 atom0745Coded := by decide +kernel
theorem atom0745Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399373919078400 : Int) atom0745Coded) := by
  have h := atom0745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0746 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0746 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 1) * (g 16) * (g 19)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346047948288000 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746Coded : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 1))]
theorem atom0746Coded_decode : atom0746 = SparsePolynomial.decodeCubic 24 atom0746Coded := by decide +kernel
theorem atom0746Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346047948288000 : Int) atom0746Coded) := by
  have h := atom0746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0747 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0747 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 1) * (g 16) * (g 20)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440027529984000 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747Coded : CoefficientMerge.Poly := [(nat_lit 980, Int.ofNat (nat_lit 1))]
theorem atom0747Coded_decode : atom0747 = SparsePolynomial.decodeCubic 24 atom0747Coded := by decide +kernel
theorem atom0747Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440027529984000 : Int) atom0747Coded) := by
  have h := atom0747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0748 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0748 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 1) * (g 16) * (g 21)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (394299305164800 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748Coded : CoefficientMerge.Poly := [(nat_lit 981, Int.ofNat (nat_lit 1))]
theorem atom0748Coded_decode : atom0748 = SparsePolynomial.decodeCubic 24 atom0748Coded := by decide +kernel
theorem atom0748Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (394299305164800 : Int) atom0748Coded) := by
  have h := atom0748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0749 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0749 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 1) * (g 16) * (g 22)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (288457051008000 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749Coded : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 1))]
theorem atom0749Coded_decode : atom0749 = SparsePolynomial.decodeCubic 24 atom0749Coded := by decide +kernel
theorem atom0749Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (288457051008000 : Int) atom0749Coded) := by
  have h := atom0749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0750 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0750 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 1) * (g 16) * (g 23)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (322053709824000 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750Coded : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 1))]
theorem atom0750Coded_decode : atom0750 = SparsePolynomial.decodeCubic 24 atom0750Coded := by decide +kernel
theorem atom0750Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (322053709824000 : Int) atom0750Coded) := by
  have h := atom0750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0751 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0751 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210072006144000 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751Coded : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 1))]
theorem atom0751Coded_decode : atom0751 = SparsePolynomial.decodeCubic 24 atom0751Coded := by decide +kernel
theorem atom0751Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210072006144000 : Int) atom0751Coded) := by
  have h := atom0751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0752 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0752 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 1) * (g 17) * (g 18)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410533430630400 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752Coded : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 1))]
theorem atom0752Coded_decode : atom0752 = SparsePolynomial.decodeCubic 24 atom0752Coded := by decide +kernel
theorem atom0752Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (410533430630400 : Int) atom0752Coded) := by
  have h := atom0752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0753 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0753 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 1) * (g 17) * (g 19)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (359248645324800 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753Coded : CoefficientMerge.Poly := [(nat_lit 1003, Int.ofNat (nat_lit 1))]
theorem atom0753Coded_decode : atom0753 = SparsePolynomial.decodeCubic 24 atom0753Coded := by decide +kernel
theorem atom0753Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (359248645324800 : Int) atom0753Coded) := by
  have h := atom0753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0754 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0754 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 1) * (g 17) * (g 20)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (455269412505600 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754Coded : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 1))]
theorem atom0754Coded_decode : atom0754 = SparsePolynomial.decodeCubic 24 atom0754Coded := by decide +kernel
theorem atom0754Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (455269412505600 : Int) atom0754Coded) := by
  have h := atom0754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0755 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0755 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 1) * (g 17) * (g 21)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411582373171200 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755Coded : CoefficientMerge.Poly := [(nat_lit 1005, Int.ofNat (nat_lit 1))]
theorem atom0755Coded_decode : atom0755 = SparsePolynomial.decodeCubic 24 atom0755Coded := by decide +kernel
theorem atom0755Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (411582373171200 : Int) atom0755Coded) := by
  have h := atom0755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0756 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0756 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 1) * (g 17) * (g 22)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (306657621580800 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756Coded : CoefficientMerge.Poly := [(nat_lit 1006, Int.ofNat (nat_lit 1))]
theorem atom0756Coded_decode : atom0756 = SparsePolynomial.decodeCubic 24 atom0756Coded := by decide +kernel
theorem atom0756Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (306657621580800 : Int) atom0756Coded) := by
  have h := atom0756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0757 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0757 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 1) * (g 17) * (g 23)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342295465881600 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757Coded : CoefficientMerge.Poly := [(nat_lit 1007, Int.ofNat (nat_lit 1))]
theorem atom0757Coded_decode : atom0757 = SparsePolynomial.decodeCubic 24 atom0757Coded := by decide +kernel
theorem atom0757Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342295465881600 : Int) atom0757Coded) := by
  have h := atom0757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0758 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0758 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 1) * (g 18) * (g 18)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (240477164928000 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758Coded : CoefficientMerge.Poly := [(nat_lit 1026, Int.ofNat (nat_lit 1))]
theorem atom0758Coded_decode : atom0758 = SparsePolynomial.decodeCubic 24 atom0758Coded := by decide +kernel
theorem atom0758Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (240477164928000 : Int) atom0758Coded) := by
  have h := atom0758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0759 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0759 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 1) * (g 18) * (g 19)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (398116218931200 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759Coded : CoefficientMerge.Poly := [(nat_lit 1027, Int.ofNat (nat_lit 1))]
theorem atom0759Coded_decode : atom0759 = SparsePolynomial.decodeCubic 24 atom0759Coded := by decide +kernel
theorem atom0759Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (398116218931200 : Int) atom0759Coded) := by
  have h := atom0759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0760 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0760 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 1) * (g 18) * (g 20)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (529772682700800 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760Coded : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 1))]
theorem atom0760Coded_decode : atom0760 = SparsePolynomial.decodeCubic 24 atom0760Coded := by decide +kernel
theorem atom0760Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (529772682700800 : Int) atom0760Coded) := by
  have h := atom0760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0761 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0761 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 1) * (g 18) * (g 21)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (485943894374400 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761Coded : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 1))]
theorem atom0761Coded_decode : atom0761 = SparsePolynomial.decodeCubic 24 atom0761Coded := by decide +kernel
theorem atom0761Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (485943894374400 : Int) atom0761Coded) := by
  have h := atom0761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0762 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0762 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 1) * (g 18) * (g 22)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318619088793600 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762Coded : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 1))]
theorem atom0762Coded_decode : atom0762 = SparsePolynomial.decodeCubic 24 atom0762Coded := by decide +kernel
theorem atom0762Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (318619088793600 : Int) atom0762Coded) := by
  have h := atom0762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0763 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0763 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 1) * (g 18) * (g 23)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349384687344000 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763Coded : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 1))]
theorem atom0763Coded_decode : atom0763 = SparsePolynomial.decodeCubic 24 atom0763Coded := by decide +kernel
theorem atom0763Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349384687344000 : Int) atom0763Coded) := by
  have h := atom0763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0764 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0764 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 1) * (g 19) * (g 19)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142023985044480 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764Coded : CoefficientMerge.Poly := [(nat_lit 1051, Int.ofNat (nat_lit 1))]
theorem atom0764Coded_decode : atom0764 = SparsePolynomial.decodeCubic 24 atom0764Coded := by decide +kernel
theorem atom0764Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142023985044480 : Int) atom0764Coded) := by
  have h := atom0764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0765 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0765 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 1) * (g 19) * (g 20)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386251828300800 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765Coded : CoefficientMerge.Poly := [(nat_lit 1052, Int.ofNat (nat_lit 1))]
theorem atom0765Coded_decode : atom0765 = SparsePolynomial.decodeCubic 24 atom0765Coded := by decide +kernel
theorem atom0765Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (386251828300800 : Int) atom0765Coded) := by
  have h := atom0765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0766 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0766 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 1) * (g 19) * (g 21)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405395029670400 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766Coded : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 1))]
theorem atom0766Coded_decode : atom0766 = SparsePolynomial.decodeCubic 24 atom0766Coded := by decide +kernel
theorem atom0766Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (405395029670400 : Int) atom0766Coded) := by
  have h := atom0766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0767 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0767 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 1) * (g 19) * (g 22)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291706968806400 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767Coded : CoefficientMerge.Poly := [(nat_lit 1054, Int.ofNat (nat_lit 1))]
theorem atom0767Coded_decode : atom0767 = SparsePolynomial.decodeCubic 24 atom0767Coded := by decide +kernel
theorem atom0767Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291706968806400 : Int) atom0767Coded) := by
  have h := atom0767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0768 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0768 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 1) * (g 19) * (g 23)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283733641699200 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768Coded : CoefficientMerge.Poly := [(nat_lit 1055, Int.ofNat (nat_lit 1))]
theorem atom0768Coded_decode : atom0768 = SparsePolynomial.decodeCubic 24 atom0768Coded := by decide +kernel
theorem atom0768Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283733641699200 : Int) atom0768Coded) := by
  have h := atom0768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block011 : CoefficientMerge.Poly := [(nat_lit 852, Int.ofNat (nat_lit 394708547851200)), (nat_lit 853, Int.ofNat (nat_lit 353450265078240)), (nat_lit 854, Int.ofNat (nat_lit 321640443169056)), (nat_lit 855, Int.ofNat (nat_lit 318715903738656)), (nat_lit 856, Int.ofNat (nat_lit 299599119226656)), (nat_lit 857, Int.ofNat (nat_lit 295381442401056)), (nat_lit 858, Int.ofNat (nat_lit 349182426719808)), (nat_lit 859, Int.ofNat (nat_lit 315381779675424)), (nat_lit 860, Int.ofNat (nat_lit 369424182777408)), (nat_lit 861, Int.ofNat (nat_lit 359408125596960)), (nat_lit 862, Int.ofNat (nat_lit 330379014712320)), (nat_lit 863, Int.ofNat (nat_lit 338126709026304)), (nat_lit 876, Int.ofNat (nat_lit 242832577553280)), (nat_lit 877, Int.ofNat (nat_lit 435085192840320)), (nat_lit 878, Int.ofNat (nat_lit 385560346343040)), (nat_lit 879, Int.ofNat (nat_lit 379386155583936)), (nat_lit 880, Int.ofNat (nat_lit 357728520390336)), (nat_lit 881, Int.ofNat (nat_lit 350969992883136)), (nat_lit 882, Int.ofNat (nat_lit 415062219800448)), (nat_lit 883, Int.ofNat (nat_lit 361270446634944)), (nat_lit 884, Int.ofNat (nat_lit 439386346827648)), (nat_lit 885, Int.ofNat (nat_lit 390978726874560)), (nat_lit 886, Int.ofNat (nat_lit 325176814433280)), (nat_lit 887, Int.ofNat (nat_lit 324378474292224)), (nat_lit 901, Int.ofNat (nat_lit 241883189856000)), (nat_lit 902, Int.ofNat (nat_lit 422611559979840)), (nat_lit 903, Int.ofNat (nat_lit 385974487301760)), (nat_lit 904, Int.ofNat (nat_lit 358553364624000)), (nat_lit 905, Int.ofNat (nat_lit 348743690064000)), (nat_lit 906, Int.ofNat (nat_lit 407775787372800)), (nat_lit 907, Int.ofNat (nat_lit 355536072460800)), (nat_lit 908, Int.ofNat (nat_lit 436182285369600)), (nat_lit 909, Int.ofNat (nat_lit 384330504096000)), (nat_lit 910, Int.ofNat (nat_lit 327597538800000)), (nat_lit 911, Int.ofNat (nat_lit 327207015273600)), (nat_lit 926, Int.ofNat (nat_lit 230358944692800)), (nat_lit 927, Int.ofNat (nat_lit 415536541842240)), (nat_lit 928, Int.ofNat (nat_lit 358531991415360)), (nat_lit 929, Int.ofNat (nat_lit 344356141852800)), (nat_lit 930, Int.ofNat (nat_lit 393140829312000)), (nat_lit 931, Int.ofNat (nat_lit 345302980822800)), (nat_lit 932, Int.ofNat (nat_lit 425629698278400)), (nat_lit 933, Int.ofNat (nat_lit 375819102489600)), (nat_lit 934, Int.ofNat (nat_lit 323273321641200)), (nat_lit 935, Int.ofNat (nat_lit 321024479252400)), (nat_lit 951, Int.ofNat (nat_lit 236349692006400)), (nat_lit 952, Int.ofNat (nat_lit 402531313443840)), (nat_lit 953, Int.ofNat (nat_lit 362157076915200)), (nat_lit 954, Int.ofNat (nat_lit 408079884441600)), (nat_lit 955, Int.ofNat (nat_lit 352712728166400)), (nat_lit 956, Int.ofNat (nat_lit 444651124377600)), (nat_lit 957, Int.ofNat (nat_lit 396881714073600)), (nat_lit 958, Int.ofNat (nat_lit 308523875923200)), (nat_lit 959, Int.ofNat (nat_lit 301811953766400)), (nat_lit 976, Int.ofNat (nat_lit 218895236582400)), (nat_lit 977, Int.ofNat (nat_lit 376667448729600)), (nat_lit 978, Int.ofNat (nat_lit 399373919078400)), (nat_lit 979, Int.ofNat (nat_lit 346047948288000)), (nat_lit 980, Int.ofNat (nat_lit 440027529984000)), (nat_lit 981, Int.ofNat (nat_lit 394299305164800)), (nat_lit 982, Int.ofNat (nat_lit 288457051008000)), (nat_lit 983, Int.ofNat (nat_lit 322053709824000)), (nat_lit 1001, Int.ofNat (nat_lit 210072006144000)), (nat_lit 1002, Int.ofNat (nat_lit 410533430630400)), (nat_lit 1003, Int.ofNat (nat_lit 359248645324800)), (nat_lit 1004, Int.ofNat (nat_lit 455269412505600)), (nat_lit 1005, Int.ofNat (nat_lit 411582373171200)), (nat_lit 1006, Int.ofNat (nat_lit 306657621580800)), (nat_lit 1007, Int.ofNat (nat_lit 342295465881600)), (nat_lit 1026, Int.ofNat (nat_lit 240477164928000)), (nat_lit 1027, Int.ofNat (nat_lit 398116218931200)), (nat_lit 1028, Int.ofNat (nat_lit 529772682700800)), (nat_lit 1029, Int.ofNat (nat_lit 485943894374400)), (nat_lit 1030, Int.ofNat (nat_lit 318619088793600)), (nat_lit 1031, Int.ofNat (nat_lit 349384687344000)), (nat_lit 1051, Int.ofNat (nat_lit 142023985044480)), (nat_lit 1052, Int.ofNat (nat_lit 386251828300800)), (nat_lit 1053, Int.ofNat (nat_lit 405395029670400)), (nat_lit 1054, Int.ofNat (nat_lit 291706968806400)), (nat_lit 1055, Int.ofNat (nat_lit 283733641699200))]
theorem block011_data : block011 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (394708547851200 : Int) atom0689Coded) (CoefficientMerge.scale (353450265078240 : Int) atom0690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321640443169056 : Int) atom0691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (318715903738656 : Int) atom0692Coded) (CoefficientMerge.scale (299599119226656 : Int) atom0693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (295381442401056 : Int) atom0694Coded) (CoefficientMerge.scale (349182426719808 : Int) atom0695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315381779675424 : Int) atom0696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369424182777408 : Int) atom0697Coded) (CoefficientMerge.scale (359408125596960 : Int) atom0698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330379014712320 : Int) atom0699Coded) (CoefficientMerge.scale (338126709026304 : Int) atom0700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242832577553280 : Int) atom0701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (435085192840320 : Int) atom0702Coded) (CoefficientMerge.scale (385560346343040 : Int) atom0703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379386155583936 : Int) atom0704Coded) (CoefficientMerge.scale (357728520390336 : Int) atom0705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350969992883136 : Int) atom0706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415062219800448 : Int) atom0707Coded) (CoefficientMerge.scale (361270446634944 : Int) atom0708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439386346827648 : Int) atom0709Coded) (CoefficientMerge.scale (390978726874560 : Int) atom0710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (325176814433280 : Int) atom0711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324378474292224 : Int) atom0712Coded) (CoefficientMerge.scale (241883189856000 : Int) atom0713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422611559979840 : Int) atom0714Coded) (CoefficientMerge.scale (385974487301760 : Int) atom0715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358553364624000 : Int) atom0716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348743690064000 : Int) atom0717Coded) (CoefficientMerge.scale (407775787372800 : Int) atom0718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355536072460800 : Int) atom0719Coded) (CoefficientMerge.scale (436182285369600 : Int) atom0720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (384330504096000 : Int) atom0721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (327597538800000 : Int) atom0722Coded) (CoefficientMerge.scale (327207015273600 : Int) atom0723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230358944692800 : Int) atom0724Coded) (CoefficientMerge.scale (415536541842240 : Int) atom0725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358531991415360 : Int) atom0726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344356141852800 : Int) atom0727Coded) (CoefficientMerge.scale (393140829312000 : Int) atom0728Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (345302980822800 : Int) atom0729Coded) (CoefficientMerge.scale (425629698278400 : Int) atom0730Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375819102489600 : Int) atom0731Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323273321641200 : Int) atom0732Coded) (CoefficientMerge.scale (321024479252400 : Int) atom0733Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (236349692006400 : Int) atom0734Coded) (CoefficientMerge.scale (402531313443840 : Int) atom0735Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (362157076915200 : Int) atom0736Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (408079884441600 : Int) atom0737Coded) (CoefficientMerge.scale (352712728166400 : Int) atom0738Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444651124377600 : Int) atom0739Coded) (CoefficientMerge.scale (396881714073600 : Int) atom0740Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (308523875923200 : Int) atom0741Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (301811953766400 : Int) atom0742Coded) (CoefficientMerge.scale (218895236582400 : Int) atom0743Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (376667448729600 : Int) atom0744Coded) (CoefficientMerge.scale (399373919078400 : Int) atom0745Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346047948288000 : Int) atom0746Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (440027529984000 : Int) atom0747Coded) (CoefficientMerge.scale (394299305164800 : Int) atom0748Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (288457051008000 : Int) atom0749Coded) (CoefficientMerge.scale (322053709824000 : Int) atom0750Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210072006144000 : Int) atom0751Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (410533430630400 : Int) atom0752Coded) (CoefficientMerge.scale (359248645324800 : Int) atom0753Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455269412505600 : Int) atom0754Coded) (CoefficientMerge.scale (411582373171200 : Int) atom0755Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (306657621580800 : Int) atom0756Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342295465881600 : Int) atom0757Coded) (CoefficientMerge.scale (240477164928000 : Int) atom0758Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (398116218931200 : Int) atom0759Coded) (CoefficientMerge.scale (529772682700800 : Int) atom0760Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (485943894374400 : Int) atom0761Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (318619088793600 : Int) atom0762Coded) (CoefficientMerge.scale (349384687344000 : Int) atom0763Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142023985044480 : Int) atom0764Coded) (CoefficientMerge.scale (386251828300800 : Int) atom0765Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (405395029670400 : Int) atom0766Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291706968806400 : Int) atom0767Coded) (CoefficientMerge.scale (283733641699200 : Int) atom0768Coded)))))))) := by decide +kernel
theorem block011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block011 := by
  rw [block011_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0689Coded_nonneg g hg hA hB) (atom0690Coded_nonneg g hg hA hB)) (add_nonneg (atom0691Coded_nonneg g hg hA hB) (add_nonneg (atom0692Coded_nonneg g hg hA hB) (atom0693Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0694Coded_nonneg g hg hA hB) (atom0695Coded_nonneg g hg hA hB)) (add_nonneg (atom0696Coded_nonneg g hg hA hB) (add_nonneg (atom0697Coded_nonneg g hg hA hB) (atom0698Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0699Coded_nonneg g hg hA hB) (atom0700Coded_nonneg g hg hA hB)) (add_nonneg (atom0701Coded_nonneg g hg hA hB) (add_nonneg (atom0702Coded_nonneg g hg hA hB) (atom0703Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0704Coded_nonneg g hg hA hB) (atom0705Coded_nonneg g hg hA hB)) (add_nonneg (atom0706Coded_nonneg g hg hA hB) (add_nonneg (atom0707Coded_nonneg g hg hA hB) (atom0708Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0709Coded_nonneg g hg hA hB) (atom0710Coded_nonneg g hg hA hB)) (add_nonneg (atom0711Coded_nonneg g hg hA hB) (add_nonneg (atom0712Coded_nonneg g hg hA hB) (atom0713Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0714Coded_nonneg g hg hA hB) (atom0715Coded_nonneg g hg hA hB)) (add_nonneg (atom0716Coded_nonneg g hg hA hB) (add_nonneg (atom0717Coded_nonneg g hg hA hB) (atom0718Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0719Coded_nonneg g hg hA hB) (atom0720Coded_nonneg g hg hA hB)) (add_nonneg (atom0721Coded_nonneg g hg hA hB) (add_nonneg (atom0722Coded_nonneg g hg hA hB) (atom0723Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0724Coded_nonneg g hg hA hB) (atom0725Coded_nonneg g hg hA hB)) (add_nonneg (atom0726Coded_nonneg g hg hA hB) (add_nonneg (atom0727Coded_nonneg g hg hA hB) (atom0728Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0729Coded_nonneg g hg hA hB) (atom0730Coded_nonneg g hg hA hB)) (add_nonneg (atom0731Coded_nonneg g hg hA hB) (add_nonneg (atom0732Coded_nonneg g hg hA hB) (atom0733Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0734Coded_nonneg g hg hA hB) (atom0735Coded_nonneg g hg hA hB)) (add_nonneg (atom0736Coded_nonneg g hg hA hB) (add_nonneg (atom0737Coded_nonneg g hg hA hB) (atom0738Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0739Coded_nonneg g hg hA hB) (atom0740Coded_nonneg g hg hA hB)) (add_nonneg (atom0741Coded_nonneg g hg hA hB) (add_nonneg (atom0742Coded_nonneg g hg hA hB) (atom0743Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0744Coded_nonneg g hg hA hB) (atom0745Coded_nonneg g hg hA hB)) (add_nonneg (atom0746Coded_nonneg g hg hA hB) (add_nonneg (atom0747Coded_nonneg g hg hA hB) (atom0748Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0749Coded_nonneg g hg hA hB) (atom0750Coded_nonneg g hg hA hB)) (add_nonneg (atom0751Coded_nonneg g hg hA hB) (add_nonneg (atom0752Coded_nonneg g hg hA hB) (atom0753Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0754Coded_nonneg g hg hA hB) (atom0755Coded_nonneg g hg hA hB)) (add_nonneg (atom0756Coded_nonneg g hg hA hB) (add_nonneg (atom0757Coded_nonneg g hg hA hB) (atom0758Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0759Coded_nonneg g hg hA hB) (atom0760Coded_nonneg g hg hA hB)) (add_nonneg (atom0761Coded_nonneg g hg hA hB) (add_nonneg (atom0762Coded_nonneg g hg hA hB) (atom0763Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0764Coded_nonneg g hg hA hB) (atom0765Coded_nonneg g hg hA hB)) (add_nonneg (atom0766Coded_nonneg g hg hA hB) (add_nonneg (atom0767Coded_nonneg g hg hA hB) (atom0768Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
