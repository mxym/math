-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0815 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0815 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0815 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0815_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13013137800 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0815Coded : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 1))]
theorem atom0815Coded_decode : atom0815 = SparsePolynomial.decodeCubic 18 atom0815Coded := by decide +kernel
theorem atom0815Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) := by
  have h := atom0815_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0815Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0816 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0816 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0816 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0816_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9515050920 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0816Coded : CoefficientMerge.Poly := [(nat_lit 1852, Int.ofNat (nat_lit 1))]
theorem atom0816Coded_decode : atom0816 = SparsePolynomial.decodeCubic 18 atom0816Coded := by decide +kernel
theorem atom0816Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded) := by
  have h := atom0816_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0816Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0817 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0817 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0817 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0817_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14900266440 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817Coded : CoefficientMerge.Poly := [(nat_lit 1853, Int.ofNat (nat_lit 1))]
theorem atom0817Coded_decode : atom0817 = SparsePolynomial.decodeCubic 18 atom0817Coded := by decide +kernel
theorem atom0817Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) := by
  have h := atom0817_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0817Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0818 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0818 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0818 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0818_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3202633728 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818Coded : CoefficientMerge.Poly := [(nat_lit 1867, Int.ofNat (nat_lit 1))]
theorem atom0818Coded_decode : atom0818 = SparsePolynomial.decodeCubic 18 atom0818Coded := by decide +kernel
theorem atom0818Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) := by
  have h := atom0818_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0818Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0819 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0819 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0819 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0819_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10330996320 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819Coded : CoefficientMerge.Poly := [(nat_lit 1868, Int.ofNat (nat_lit 1))]
theorem atom0819Coded_decode : atom0819 = SparsePolynomial.decodeCubic 18 atom0819Coded := by decide +kernel
theorem atom0819Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded) := by
  have h := atom0819_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0819Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0820 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0820 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0820 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0820_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11120842620 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820Coded : CoefficientMerge.Poly := [(nat_lit 1869, Int.ofNat (nat_lit 1))]
theorem atom0820Coded_decode : atom0820 = SparsePolynomial.decodeCubic 18 atom0820Coded := by decide +kernel
theorem atom0820Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) := by
  have h := atom0820_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0820Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0821 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0821 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0821 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0821_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8447358000 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821Coded : CoefficientMerge.Poly := [(nat_lit 1870, Int.ofNat (nat_lit 1))]
theorem atom0821Coded_decode : atom0821 = SparsePolynomial.decodeCubic 18 atom0821Coded := by decide +kernel
theorem atom0821Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded) := by
  have h := atom0821_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0821Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0822 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0822 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10737773370 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822Coded : CoefficientMerge.Poly := [(nat_lit 1871, Int.ofNat (nat_lit 1))]
theorem atom0822Coded_decode : atom0822 = SparsePolynomial.decodeCubic 18 atom0822Coded := by decide +kernel
theorem atom0822Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) := by
  have h := atom0822_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0822Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0823 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0823 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0823 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0823_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7850979000 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823Coded : CoefficientMerge.Poly := [(nat_lit 1886, Int.ofNat (nat_lit 1))]
theorem atom0823Coded_decode : atom0823 = SparsePolynomial.decodeCubic 18 atom0823Coded := by decide +kernel
theorem atom0823Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) := by
  have h := atom0823_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0823Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0824 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0824 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0824 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0824_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12484453680 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824Coded : CoefficientMerge.Poly := [(nat_lit 1887, Int.ofNat (nat_lit 1))]
theorem atom0824Coded_decode : atom0824 = SparsePolynomial.decodeCubic 18 atom0824Coded := by decide +kernel
theorem atom0824Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded) := by
  have h := atom0824_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0824Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0825 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0825 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0825 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0825_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9208198920 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825Coded : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 1))]
theorem atom0825Coded_decode : atom0825 = SparsePolynomial.decodeCubic 18 atom0825Coded := by decide +kernel
theorem atom0825Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) := by
  have h := atom0825_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0825Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0826 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0826 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0826 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0826_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12481979400 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826Coded : CoefficientMerge.Poly := [(nat_lit 1889, Int.ofNat (nat_lit 1))]
theorem atom0826Coded_decode : atom0826 = SparsePolynomial.decodeCubic 18 atom0826Coded := by decide +kernel
theorem atom0826Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded) := by
  have h := atom0826_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0826Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0827 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0827 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0827 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0827_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3495594420 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827Coded : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 1))]
theorem atom0827Coded_decode : atom0827 = SparsePolynomial.decodeCubic 18 atom0827Coded := by decide +kernel
theorem atom0827Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) := by
  have h := atom0827_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0827Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0828 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0828 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0828 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0828_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4734746820 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828Coded : CoefficientMerge.Poly := [(nat_lit 1906, Int.ofNat (nat_lit 1))]
theorem atom0828Coded_decode : atom0828 = SparsePolynomial.decodeCubic 18 atom0828Coded := by decide +kernel
theorem atom0828Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) := by
  have h := atom0828_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0828Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0829 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0829 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0829 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0829_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8199759330 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829Coded : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 1))]
theorem atom0829Coded_decode : atom0829 = SparsePolynomial.decodeCubic 18 atom0829Coded := by decide +kernel
theorem atom0829Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded) := by
  have h := atom0829_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0829Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0830 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0830 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0830 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0830_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3354207030 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830Coded : CoefficientMerge.Poly := [(nat_lit 1925, Int.ofNat (nat_lit 1))]
theorem atom0830Coded_decode : atom0830 = SparsePolynomial.decodeCubic 18 atom0830Coded := by decide +kernel
theorem atom0830Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) := by
  have h := atom0830_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0830Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0831 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0831 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0831 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0831_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3244305150 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831Coded : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 1))]
theorem atom0831Coded_decode : atom0831 = SparsePolynomial.decodeCubic 18 atom0831Coded := by decide +kernel
theorem atom0831Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded) := by
  have h := atom0831_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0831Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0832 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0832 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0832 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0832_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199002240 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832Coded : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 1))]
theorem atom0832Coded_decode : atom0832 = SparsePolynomial.decodeCubic 18 atom0832Coded := by decide +kernel
theorem atom0832Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (199002240 : Int) atom0832Coded) := by
  have h := atom0832_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0832Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0833 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0833 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0833 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0833_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833Coded : CoefficientMerge.Poly := [(nat_lit 2059, Int.ofNat (nat_lit 1))]
theorem atom0833Coded_decode : atom0833 = SparsePolynomial.decodeCubic 18 atom0833Coded := by decide +kernel
theorem atom0833Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0833Coded) := by
  have h := atom0833_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0833Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0834 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0834 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0834 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0834_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25159680 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834Coded : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 1))]
theorem atom0834Coded_decode : atom0834 = SparsePolynomial.decodeCubic 18 atom0834Coded := by decide +kernel
theorem atom0834Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (25159680 : Int) atom0834Coded) := by
  have h := atom0834_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0834Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0835 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0835 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0835 = ((g 6) * (g 6) * (g 12)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0835_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382258800 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835Coded : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 1))]
theorem atom0835Coded_decode : atom0835 = SparsePolynomial.decodeCubic 18 atom0835Coded := by decide +kernel
theorem atom0835Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (382258800 : Int) atom0835Coded) := by
  have h := atom0835_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0835Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0836 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0836 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180362880 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836Coded : CoefficientMerge.Poly := [(nat_lit 2077, Int.ofNat (nat_lit 1))]
theorem atom0836Coded_decode : atom0836 = SparsePolynomial.decodeCubic 18 atom0836Coded := by decide +kernel
theorem atom0836Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (180362880 : Int) atom0836Coded) := by
  have h := atom0836_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0836Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0837 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0837 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0837 = ((g 6) * (g 7) * (g 10)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0837_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837Coded : CoefficientMerge.Poly := [(nat_lit 2080, Int.ofNat (nat_lit 1))]
theorem atom0837Coded_decode : atom0837 = SparsePolynomial.decodeCubic 18 atom0837Coded := by decide +kernel
theorem atom0837Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0837Coded) := by
  have h := atom0837_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0837Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0838 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0838 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0838 = ((g 6) * (g 7) * (g 11)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0838_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838Coded : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 1))]
theorem atom0838Coded_decode : atom0838 = SparsePolynomial.decodeCubic 18 atom0838Coded := by decide +kernel
theorem atom0838Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (207728640 : Int) atom0838Coded) := by
  have h := atom0838_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0838Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0839 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0839 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0839 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0839_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (469928592 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839Coded : CoefficientMerge.Poly := [(nat_lit 2082, Int.ofNat (nat_lit 1))]
theorem atom0839Coded_decode : atom0839 = SparsePolynomial.decodeCubic 18 atom0839Coded := by decide +kernel
theorem atom0839Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (469928592 : Int) atom0839Coded) := by
  have h := atom0839_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0839Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0840 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0840 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0840 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0840_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840Coded : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 1))]
theorem atom0840Coded_decode : atom0840 = SparsePolynomial.decodeCubic 18 atom0840Coded := by decide +kernel
theorem atom0840Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) := by
  have h := atom0840_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0840Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0841 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0841 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0841 = ((g 6) * (g 7) * (g 16)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0841_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841Coded : CoefficientMerge.Poly := [(nat_lit 2086, Int.ofNat (nat_lit 1))]
theorem atom0841Coded_decode : atom0841 = SparsePolynomial.decodeCubic 18 atom0841Coded := by decide +kernel
theorem atom0841Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded) := by
  have h := atom0841_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0841Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0842 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0842 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0842 = ((g 6) * (g 7) * (g 17)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0842_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842Coded : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 1))]
theorem atom0842Coded_decode : atom0842 = SparsePolynomial.decodeCubic 18 atom0842Coded := by decide +kernel
theorem atom0842Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) := by
  have h := atom0842_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0842Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0843 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0843 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0843 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0843_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389278080 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843Coded : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 1))]
theorem atom0843Coded_decode : atom0843 = SparsePolynomial.decodeCubic 18 atom0843Coded := by decide +kernel
theorem atom0843Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (389278080 : Int) atom0843Coded) := by
  have h := atom0843_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0843Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0844 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0844 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0844 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0844_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (568454400 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844Coded : CoefficientMerge.Poly := [(nat_lit 2097, Int.ofNat (nat_lit 1))]
theorem atom0844Coded_decode : atom0844 = SparsePolynomial.decodeCubic 18 atom0844Coded := by decide +kernel
theorem atom0844Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (568454400 : Int) atom0844Coded) := by
  have h := atom0844_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0844Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0845 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0845 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0845 = ((g 6) * (g 8) * (g 10)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0845_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (725863680 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845Coded : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 1))]
theorem atom0845Coded_decode : atom0845 = SparsePolynomial.decodeCubic 18 atom0845Coded := by decide +kernel
theorem atom0845Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (725863680 : Int) atom0845Coded) := by
  have h := atom0845_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0845Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0846 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0846 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0846 = ((g 6) * (g 8) * (g 11)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0846_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (883272960 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846Coded : CoefficientMerge.Poly := [(nat_lit 2099, Int.ofNat (nat_lit 1))]
theorem atom0846Coded_decode : atom0846 = SparsePolynomial.decodeCubic 18 atom0846Coded := by decide +kernel
theorem atom0846Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (883272960 : Int) atom0846Coded) := by
  have h := atom0846_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0846Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0847 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0847 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0847 = ((g 6) * (g 8) * (g 12)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0847_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (757621440 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847Coded : CoefficientMerge.Poly := [(nat_lit 2100, Int.ofNat (nat_lit 1))]
theorem atom0847Coded_decode : atom0847 = SparsePolynomial.decodeCubic 18 atom0847Coded := by decide +kernel
theorem atom0847Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (757621440 : Int) atom0847Coded) := by
  have h := atom0847_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0847Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0848 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0848 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0848 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0848_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428863920 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848Coded : CoefficientMerge.Poly := [(nat_lit 2101, Int.ofNat (nat_lit 1))]
theorem atom0848Coded_decode : atom0848 = SparsePolynomial.decodeCubic 18 atom0848Coded := by decide +kernel
theorem atom0848Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (428863920 : Int) atom0848Coded) := by
  have h := atom0848_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0848Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0849 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0849 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (816511200 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849Coded : CoefficientMerge.Poly := [(nat_lit 2102, Int.ofNat (nat_lit 1))]
theorem atom0849Coded_decode : atom0849 = SparsePolynomial.decodeCubic 18 atom0849Coded := by decide +kernel
theorem atom0849Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (816511200 : Int) atom0849Coded) := by
  have h := atom0849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0850 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0850 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2272055280 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850Coded : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 1))]
theorem atom0850Coded_decode : atom0850 = SparsePolynomial.decodeCubic 18 atom0850Coded := by decide +kernel
theorem atom0850Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) := by
  have h := atom0850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0851 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0851 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4061745360 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851Coded : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 1))]
theorem atom0851Coded_decode : atom0851 = SparsePolynomial.decodeCubic 18 atom0851Coded := by decide +kernel
theorem atom0851Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded) := by
  have h := atom0851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0852 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0852 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6158118240 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852Coded : CoefficientMerge.Poly := [(nat_lit 2105, Int.ofNat (nat_lit 1))]
theorem atom0852Coded_decode : atom0852 = SparsePolynomial.decodeCubic 18 atom0852Coded := by decide +kernel
theorem atom0852Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) := by
  have h := atom0852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0853 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0853 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (852681600 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853Coded : CoefficientMerge.Poly := [(nat_lit 2115, Int.ofNat (nat_lit 1))]
theorem atom0853Coded_decode : atom0853 = SparsePolynomial.decodeCubic 18 atom0853Coded := by decide +kernel
theorem atom0853Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (852681600 : Int) atom0853Coded) := by
  have h := atom0853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0854 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0854 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1515283200 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854Coded : CoefficientMerge.Poly := [(nat_lit 2116, Int.ofNat (nat_lit 1))]
theorem atom0854Coded_decode : atom0854 = SparsePolynomial.decodeCubic 18 atom0854Coded := by decide +kernel
theorem atom0854Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded) := by
  have h := atom0854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0855 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0855 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1675918080 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855Coded : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1))]
theorem atom0855Coded_decode : atom0855 = SparsePolynomial.decodeCubic 18 atom0855Coded := by decide +kernel
theorem atom0855Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) := by
  have h := atom0855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0856 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0856 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1750199040 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856Coded : CoefficientMerge.Poly := [(nat_lit 2118, Int.ofNat (nat_lit 1))]
theorem atom0856Coded_decode : atom0856 = SparsePolynomial.decodeCubic 18 atom0856Coded := by decide +kernel
theorem atom0856Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded) := by
  have h := atom0856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0857 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0857 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1645188720 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857Coded : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 1))]
theorem atom0857Coded_decode : atom0857 = SparsePolynomial.decodeCubic 18 atom0857Coded := by decide +kernel
theorem atom0857Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) := by
  have h := atom0857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0858 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0858 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2642200800 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858Coded : CoefficientMerge.Poly := [(nat_lit 2120, Int.ofNat (nat_lit 1))]
theorem atom0858Coded_decode : atom0858 = SparsePolynomial.decodeCubic 18 atom0858Coded := by decide +kernel
theorem atom0858Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) := by
  have h := atom0858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0859 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0859 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 6) * (g 9) * (g 15)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3897057840 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859Coded : CoefficientMerge.Poly := [(nat_lit 2121, Int.ofNat (nat_lit 1))]
theorem atom0859Coded_decode : atom0859 = SparsePolynomial.decodeCubic 18 atom0859Coded := by decide +kernel
theorem atom0859Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded) := by
  have h := atom0859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0860 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0860 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 6) * (g 9) * (g 16)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5871678480 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860Coded : CoefficientMerge.Poly := [(nat_lit 2122, Int.ofNat (nat_lit 1))]
theorem atom0860Coded_decode : atom0860 = SparsePolynomial.decodeCubic 18 atom0860Coded := by decide +kernel
theorem atom0860Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) := by
  have h := atom0860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0861 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0861 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 6) * (g 9) * (g 17)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8109758880 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861Coded : CoefficientMerge.Poly := [(nat_lit 2123, Int.ofNat (nat_lit 1))]
theorem atom0861Coded_decode : atom0861 = SparsePolynomial.decodeCubic 18 atom0861Coded := by decide +kernel
theorem atom0861Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded) := by
  have h := atom0861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0862 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0862 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1439971200 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862Coded : CoefficientMerge.Poly := [(nat_lit 2134, Int.ofNat (nat_lit 1))]
theorem atom0862Coded_decode : atom0862 = SparsePolynomial.decodeCubic 18 atom0862Coded := by decide +kernel
theorem atom0862Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) := by
  have h := atom0862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0863 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0863 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2659495680 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863Coded : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 1))]
theorem atom0863Coded_decode : atom0863 = SparsePolynomial.decodeCubic 18 atom0863Coded := by decide +kernel
theorem atom0863Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) := by
  have h := atom0863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0864 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0864 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2848556160 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864Coded : CoefficientMerge.Poly := [(nat_lit 2136, Int.ofNat (nat_lit 1))]
theorem atom0864Coded_decode : atom0864 = SparsePolynomial.decodeCubic 18 atom0864Coded := by decide +kernel
theorem atom0864Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded) := by
  have h := atom0864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0865 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0865 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2847306480 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865Coded : CoefficientMerge.Poly := [(nat_lit 2137, Int.ofNat (nat_lit 1))]
theorem atom0865Coded_decode : atom0865 = SparsePolynomial.decodeCubic 18 atom0865Coded := by decide +kernel
theorem atom0865Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) := by
  have h := atom0865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0866 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0866 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4518209760 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866Coded : CoefficientMerge.Poly := [(nat_lit 2138, Int.ofNat (nat_lit 1))]
theorem atom0866Coded_decode : atom0866 = SparsePolynomial.decodeCubic 18 atom0866Coded := by decide +kernel
theorem atom0866Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded) := by
  have h := atom0866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0867 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0867 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 6) * (g 10) * (g 15)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5198213040 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867Coded : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 1))]
theorem atom0867Coded_decode : atom0867 = SparsePolynomial.decodeCubic 18 atom0867Coded := by decide +kernel
theorem atom0867Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) := by
  have h := atom0867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0868 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0868 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 6) * (g 10) * (g 16)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7168110480 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868Coded : CoefficientMerge.Poly := [(nat_lit 2140, Int.ofNat (nat_lit 1))]
theorem atom0868Coded_decode : atom0868 = SparsePolynomial.decodeCubic 18 atom0868Coded := by decide +kernel
theorem atom0868Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) := by
  have h := atom0868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0869 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0869 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 6) * (g 10) * (g 17)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9649000800 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869Coded : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 1))]
theorem atom0869Coded_decode : atom0869 = SparsePolynomial.decodeCubic 18 atom0869Coded := by decide +kernel
theorem atom0869Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded) := by
  have h := atom0869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0870 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0870 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2330513280 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870Coded : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 1))]
theorem atom0870Coded_decode : atom0870 = SparsePolynomial.decodeCubic 18 atom0870Coded := by decide +kernel
theorem atom0870Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) := by
  have h := atom0870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0871 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0871 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3823796160 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871Coded : CoefficientMerge.Poly := [(nat_lit 2154, Int.ofNat (nat_lit 1))]
theorem atom0871Coded_decode : atom0871 = SparsePolynomial.decodeCubic 18 atom0871Coded := by decide +kernel
theorem atom0871Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded) := by
  have h := atom0871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0872 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0872 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3845127600 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872Coded : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 1))]
theorem atom0872Coded_decode : atom0872 = SparsePolynomial.decodeCubic 18 atom0872Coded := by decide +kernel
theorem atom0872Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) := by
  have h := atom0872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0873 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0873 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6208074720 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873Coded : CoefficientMerge.Poly := [(nat_lit 2156, Int.ofNat (nat_lit 1))]
theorem atom0873Coded_decode : atom0873 = SparsePolynomial.decodeCubic 18 atom0873Coded := by decide +kernel
theorem atom0873Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) := by
  have h := atom0873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0874 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0874 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 6) * (g 11) * (g 15)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7191177840 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874Coded : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 1))]
theorem atom0874Coded_decode : atom0874 = SparsePolynomial.decodeCubic 18 atom0874Coded := by decide +kernel
theorem atom0874Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded) := by
  have h := atom0874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0875 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0875 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 6) * (g 11) * (g 16)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8066673360 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875Coded : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 1))]
theorem atom0875Coded_decode : atom0875 = SparsePolynomial.decodeCubic 18 atom0875Coded := by decide +kernel
theorem atom0875Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) := by
  have h := atom0875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0876 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0876 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 6) * (g 11) * (g 17)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12681810720 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876Coded : CoefficientMerge.Poly := [(nat_lit 2159, Int.ofNat (nat_lit 1))]
theorem atom0876Coded_decode : atom0876 = SparsePolynomial.decodeCubic 18 atom0876Coded := by decide +kernel
theorem atom0876Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded) := by
  have h := atom0876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0877 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0877 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3423651840 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877Coded : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 1))]
theorem atom0877Coded_decode : atom0877 = SparsePolynomial.decodeCubic 18 atom0877Coded := by decide +kernel
theorem atom0877Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) := by
  have h := atom0877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0878 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0878 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6832572120 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878Coded : CoefficientMerge.Poly := [(nat_lit 2173, Int.ofNat (nat_lit 1))]
theorem atom0878Coded_decode : atom0878 = SparsePolynomial.decodeCubic 18 atom0878Coded := by decide +kernel
theorem atom0878Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) := by
  have h := atom0878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0879 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0879 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12177540000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879Coded : CoefficientMerge.Poly := [(nat_lit 2174, Int.ofNat (nat_lit 1))]
theorem atom0879Coded_decode : atom0879 = SparsePolynomial.decodeCubic 18 atom0879Coded := by decide +kernel
theorem atom0879Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded) := by
  have h := atom0879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0880 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0880 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 6) * (g 12) * (g 15)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12748840200 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880Coded : CoefficientMerge.Poly := [(nat_lit 2175, Int.ofNat (nat_lit 1))]
theorem atom0880Coded_decode : atom0880 = SparsePolynomial.decodeCubic 18 atom0880Coded := by decide +kernel
theorem atom0880Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) := by
  have h := atom0880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0881 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0881 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 6) * (g 12) * (g 16)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9605408040 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881Coded : CoefficientMerge.Poly := [(nat_lit 2176, Int.ofNat (nat_lit 1))]
theorem atom0881Coded_decode : atom0881 = SparsePolynomial.decodeCubic 18 atom0881Coded := by decide +kernel
theorem atom0881Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded) := by
  have h := atom0881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0882 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0882 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 6) * (g 12) * (g 17)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15345278280 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882Coded : CoefficientMerge.Poly := [(nat_lit 2177, Int.ofNat (nat_lit 1))]
theorem atom0882Coded_decode : atom0882 = SparsePolynomial.decodeCubic 18 atom0882Coded := by decide +kernel
theorem atom0882Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) := by
  have h := atom0882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0883 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0883 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2714923008 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883Coded : CoefficientMerge.Poly := [(nat_lit 2191, Int.ofNat (nat_lit 1))]
theorem atom0883Coded_decode : atom0883 = SparsePolynomial.decodeCubic 18 atom0883Coded := by decide +kernel
theorem atom0883Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) := by
  have h := atom0883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0884 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0884 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9583020000 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884Coded : CoefficientMerge.Poly := [(nat_lit 2192, Int.ofNat (nat_lit 1))]
theorem atom0884Coded_decode : atom0884 = SparsePolynomial.decodeCubic 18 atom0884Coded := by decide +kernel
theorem atom0884Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded) := by
  have h := atom0884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0885 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0885 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 6) * (g 13) * (g 15)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10709800380 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885Coded : CoefficientMerge.Poly := [(nat_lit 2193, Int.ofNat (nat_lit 1))]
theorem atom0885Coded_decode : atom0885 = SparsePolynomial.decodeCubic 18 atom0885Coded := by decide +kernel
theorem atom0885Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) := by
  have h := atom0885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0886 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0886 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 6) * (g 13) * (g 16)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8121848400 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886Coded : CoefficientMerge.Poly := [(nat_lit 2194, Int.ofNat (nat_lit 1))]
theorem atom0886Coded_decode : atom0886 = SparsePolynomial.decodeCubic 18 atom0886Coded := by decide +kernel
theorem atom0886Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded) := by
  have h := atom0886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0887 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0887 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 6) * (g 13) * (g 17)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11055343770 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887Coded : CoefficientMerge.Poly := [(nat_lit 2195, Int.ofNat (nat_lit 1))]
theorem atom0887Coded_decode : atom0887 = SparsePolynomial.decodeCubic 18 atom0887Coded := by decide +kernel
theorem atom0887Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) := by
  have h := atom0887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0888 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0888 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7705827000 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888Coded : CoefficientMerge.Poly := [(nat_lit 2210, Int.ofNat (nat_lit 1))]
theorem atom0888Coded_decode : atom0888 = SparsePolynomial.decodeCubic 18 atom0888Coded := by decide +kernel
theorem atom0888Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) := by
  have h := atom0888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0889 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0889 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 6) * (g 14) * (g 15)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12583600560 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889Coded : CoefficientMerge.Poly := [(nat_lit 2211, Int.ofNat (nat_lit 1))]
theorem atom0889Coded_decode : atom0889 = SparsePolynomial.decodeCubic 18 atom0889Coded := by decide +kernel
theorem atom0889Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded) := by
  have h := atom0889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0890 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0890 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 6) * (g 14) * (g 16)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9594135720 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890Coded : CoefficientMerge.Poly := [(nat_lit 2212, Int.ofNat (nat_lit 1))]
theorem atom0890Coded_decode : atom0890 = SparsePolynomial.decodeCubic 18 atom0890Coded := by decide +kernel
theorem atom0890Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) := by
  have h := atom0890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0891 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0891 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 6) * (g 14) * (g 17)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13657509000 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891Coded : CoefficientMerge.Poly := [(nat_lit 2213, Int.ofNat (nat_lit 1))]
theorem atom0891Coded_decode : atom0891 = SparsePolynomial.decodeCubic 18 atom0891Coded := by decide +kernel
theorem atom0891Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded) := by
  have h := atom0891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0892 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0892 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3582383220 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892Coded : CoefficientMerge.Poly := [(nat_lit 2229, Int.ofNat (nat_lit 1))]
theorem atom0892Coded_decode : atom0892 = SparsePolynomial.decodeCubic 18 atom0892Coded := by decide +kernel
theorem atom0892Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) := by
  have h := atom0892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0893 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0893 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 6) * (g 15) * (g 16)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5086811700 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893Coded : CoefficientMerge.Poly := [(nat_lit 2230, Int.ofNat (nat_lit 1))]
theorem atom0893Coded_decode : atom0893 = SparsePolynomial.decodeCubic 18 atom0893Coded := by decide +kernel
theorem atom0893Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) := by
  have h := atom0893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0894 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0894 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 6) * (g 15) * (g 17)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9511338690 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894Coded : CoefficientMerge.Poly := [(nat_lit 2231, Int.ofNat (nat_lit 1))]
theorem atom0894Coded_decode : atom0894 = SparsePolynomial.decodeCubic 18 atom0894Coded := by decide +kernel
theorem atom0894Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded) := by
  have h := atom0894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block011 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680)), (nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680)), (nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400)), (nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200)), (nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160)), (nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840)), (nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000)), (nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
def block011_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800))]
theorem block011_data_flat000_step : block011_data_flat000 = (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) := by decide +kernel
theorem block011_data_flat000_original : block011_data_flat000 = (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) := by
  rw [block011_data_flat000_step]
def block011_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1852, Int.ofNat (nat_lit 9515050920))]
theorem block011_data_flat001_step : block011_data_flat001 = (CoefficientMerge.scale (9515050920 : Int) atom0816Coded) := by decide +kernel
theorem block011_data_flat001_original : block011_data_flat001 = (CoefficientMerge.scale (9515050920 : Int) atom0816Coded) := by
  rw [block011_data_flat001_step]
def block011_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920))]
theorem block011_data_flat002_step : block011_data_flat002 = (CoefficientMerge.fastMerge block011_data_flat000 block011_data_flat001) := by decide +kernel
theorem block011_data_flat002_original : block011_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) := by
  rw [block011_data_flat002_step, block011_data_flat000_original, block011_data_flat001_original]
def block011_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1853, Int.ofNat (nat_lit 14900266440))]
theorem block011_data_flat003_step : block011_data_flat003 = (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) := by decide +kernel
theorem block011_data_flat003_original : block011_data_flat003 = (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) := by
  rw [block011_data_flat003_step]
def block011_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1867, Int.ofNat (nat_lit 3202633728))]
theorem block011_data_flat004_step : block011_data_flat004 = (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) := by decide +kernel
theorem block011_data_flat004_original : block011_data_flat004 = (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) := by
  rw [block011_data_flat004_step]
def block011_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1868, Int.ofNat (nat_lit 10330996320))]
theorem block011_data_flat005_step : block011_data_flat005 = (CoefficientMerge.scale (10330996320 : Int) atom0819Coded) := by decide +kernel
theorem block011_data_flat005_original : block011_data_flat005 = (CoefficientMerge.scale (10330996320 : Int) atom0819Coded) := by
  rw [block011_data_flat005_step]
def block011_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320))]
theorem block011_data_flat006_step : block011_data_flat006 = (CoefficientMerge.fastMerge block011_data_flat004 block011_data_flat005) := by decide +kernel
theorem block011_data_flat006_original : block011_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)) := by
  rw [block011_data_flat006_step, block011_data_flat004_original, block011_data_flat005_original]
def block011_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320))]
theorem block011_data_flat007_step : block011_data_flat007 = (CoefficientMerge.fastMerge block011_data_flat003 block011_data_flat006) := by decide +kernel
theorem block011_data_flat007_original : block011_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded))) := by
  rw [block011_data_flat007_step, block011_data_flat003_original, block011_data_flat006_original]
def block011_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320))]
theorem block011_data_flat008_step : block011_data_flat008 = (CoefficientMerge.fastMerge block011_data_flat002 block011_data_flat007) := by decide +kernel
theorem block011_data_flat008_original : block011_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) := by
  rw [block011_data_flat008_step, block011_data_flat002_original, block011_data_flat007_original]
def block011_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1869, Int.ofNat (nat_lit 11120842620))]
theorem block011_data_flat009_step : block011_data_flat009 = (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) := by decide +kernel
theorem block011_data_flat009_original : block011_data_flat009 = (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) := by
  rw [block011_data_flat009_step]
def block011_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1870, Int.ofNat (nat_lit 8447358000))]
theorem block011_data_flat010_step : block011_data_flat010 = (CoefficientMerge.scale (8447358000 : Int) atom0821Coded) := by decide +kernel
theorem block011_data_flat010_original : block011_data_flat010 = (CoefficientMerge.scale (8447358000 : Int) atom0821Coded) := by
  rw [block011_data_flat010_step]
def block011_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000))]
theorem block011_data_flat011_step : block011_data_flat011 = (CoefficientMerge.fastMerge block011_data_flat009 block011_data_flat010) := by decide +kernel
theorem block011_data_flat011_original : block011_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) := by
  rw [block011_data_flat011_step, block011_data_flat009_original, block011_data_flat010_original]
def block011_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1871, Int.ofNat (nat_lit 10737773370))]
theorem block011_data_flat012_step : block011_data_flat012 = (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) := by decide +kernel
theorem block011_data_flat012_original : block011_data_flat012 = (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) := by
  rw [block011_data_flat012_step]
def block011_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1886, Int.ofNat (nat_lit 7850979000))]
theorem block011_data_flat013_step : block011_data_flat013 = (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) := by decide +kernel
theorem block011_data_flat013_original : block011_data_flat013 = (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) := by
  rw [block011_data_flat013_step]
def block011_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1887, Int.ofNat (nat_lit 12484453680))]
theorem block011_data_flat014_step : block011_data_flat014 = (CoefficientMerge.scale (12484453680 : Int) atom0824Coded) := by decide +kernel
theorem block011_data_flat014_original : block011_data_flat014 = (CoefficientMerge.scale (12484453680 : Int) atom0824Coded) := by
  rw [block011_data_flat014_step]
def block011_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680))]
theorem block011_data_flat015_step : block011_data_flat015 = (CoefficientMerge.fastMerge block011_data_flat013 block011_data_flat014) := by decide +kernel
theorem block011_data_flat015_original : block011_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded)) := by
  rw [block011_data_flat015_step, block011_data_flat013_original, block011_data_flat014_original]
def block011_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680))]
theorem block011_data_flat016_step : block011_data_flat016 = (CoefficientMerge.fastMerge block011_data_flat012 block011_data_flat015) := by decide +kernel
theorem block011_data_flat016_original : block011_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))) := by
  rw [block011_data_flat016_step, block011_data_flat012_original, block011_data_flat015_original]
def block011_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680))]
theorem block011_data_flat017_step : block011_data_flat017 = (CoefficientMerge.fastMerge block011_data_flat011 block011_data_flat016) := by decide +kernel
theorem block011_data_flat017_original : block011_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded)))) := by
  rw [block011_data_flat017_step, block011_data_flat011_original, block011_data_flat016_original]
def block011_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680))]
theorem block011_data_flat018_step : block011_data_flat018 = (CoefficientMerge.fastMerge block011_data_flat008 block011_data_flat017) := by decide +kernel
theorem block011_data_flat018_original : block011_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) := by
  rw [block011_data_flat018_step, block011_data_flat008_original, block011_data_flat017_original]
def block011_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 9208198920))]
theorem block011_data_flat019_step : block011_data_flat019 = (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) := by decide +kernel
theorem block011_data_flat019_original : block011_data_flat019 = (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) := by
  rw [block011_data_flat019_step]
def block011_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1889, Int.ofNat (nat_lit 12481979400))]
theorem block011_data_flat020_step : block011_data_flat020 = (CoefficientMerge.scale (12481979400 : Int) atom0826Coded) := by decide +kernel
theorem block011_data_flat020_original : block011_data_flat020 = (CoefficientMerge.scale (12481979400 : Int) atom0826Coded) := by
  rw [block011_data_flat020_step]
def block011_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400))]
theorem block011_data_flat021_step : block011_data_flat021 = (CoefficientMerge.fastMerge block011_data_flat019 block011_data_flat020) := by decide +kernel
theorem block011_data_flat021_original : block011_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) := by
  rw [block011_data_flat021_step, block011_data_flat019_original, block011_data_flat020_original]
def block011_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 3495594420))]
theorem block011_data_flat022_step : block011_data_flat022 = (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) := by decide +kernel
theorem block011_data_flat022_original : block011_data_flat022 = (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) := by
  rw [block011_data_flat022_step]
def block011_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1906, Int.ofNat (nat_lit 4734746820))]
theorem block011_data_flat023_step : block011_data_flat023 = (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) := by decide +kernel
theorem block011_data_flat023_original : block011_data_flat023 = (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) := by
  rw [block011_data_flat023_step]
def block011_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 8199759330))]
theorem block011_data_flat024_step : block011_data_flat024 = (CoefficientMerge.scale (8199759330 : Int) atom0829Coded) := by decide +kernel
theorem block011_data_flat024_original : block011_data_flat024 = (CoefficientMerge.scale (8199759330 : Int) atom0829Coded) := by
  rw [block011_data_flat024_step]
def block011_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330))]
theorem block011_data_flat025_step : block011_data_flat025 = (CoefficientMerge.fastMerge block011_data_flat023 block011_data_flat024) := by decide +kernel
theorem block011_data_flat025_original : block011_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)) := by
  rw [block011_data_flat025_step, block011_data_flat023_original, block011_data_flat024_original]
def block011_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330))]
theorem block011_data_flat026_step : block011_data_flat026 = (CoefficientMerge.fastMerge block011_data_flat022 block011_data_flat025) := by decide +kernel
theorem block011_data_flat026_original : block011_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded))) := by
  rw [block011_data_flat026_step, block011_data_flat022_original, block011_data_flat025_original]
def block011_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330))]
theorem block011_data_flat027_step : block011_data_flat027 = (CoefficientMerge.fastMerge block011_data_flat021 block011_data_flat026) := by decide +kernel
theorem block011_data_flat027_original : block011_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) := by
  rw [block011_data_flat027_step, block011_data_flat021_original, block011_data_flat026_original]
def block011_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1925, Int.ofNat (nat_lit 3354207030))]
theorem block011_data_flat028_step : block011_data_flat028 = (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) := by decide +kernel
theorem block011_data_flat028_original : block011_data_flat028 = (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) := by
  rw [block011_data_flat028_step]
def block011_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 3244305150))]
theorem block011_data_flat029_step : block011_data_flat029 = (CoefficientMerge.scale (3244305150 : Int) atom0831Coded) := by decide +kernel
theorem block011_data_flat029_original : block011_data_flat029 = (CoefficientMerge.scale (3244305150 : Int) atom0831Coded) := by
  rw [block011_data_flat029_step]
def block011_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150))]
theorem block011_data_flat030_step : block011_data_flat030 = (CoefficientMerge.fastMerge block011_data_flat028 block011_data_flat029) := by decide +kernel
theorem block011_data_flat030_original : block011_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) := by
  rw [block011_data_flat030_step, block011_data_flat028_original, block011_data_flat029_original]
def block011_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 199002240))]
theorem block011_data_flat031_step : block011_data_flat031 = (CoefficientMerge.scale (199002240 : Int) atom0832Coded) := by decide +kernel
theorem block011_data_flat031_original : block011_data_flat031 = (CoefficientMerge.scale (199002240 : Int) atom0832Coded) := by
  rw [block011_data_flat031_step]
def block011_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2059, Int.ofNat (nat_lit 103864320))]
theorem block011_data_flat032_step : block011_data_flat032 = (CoefficientMerge.scale (103864320 : Int) atom0833Coded) := by decide +kernel
theorem block011_data_flat032_original : block011_data_flat032 = (CoefficientMerge.scale (103864320 : Int) atom0833Coded) := by
  rw [block011_data_flat032_step]
def block011_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat033_step : block011_data_flat033 = (CoefficientMerge.scale (25159680 : Int) atom0834Coded) := by decide +kernel
theorem block011_data_flat033_original : block011_data_flat033 = (CoefficientMerge.scale (25159680 : Int) atom0834Coded) := by
  rw [block011_data_flat033_step]
def block011_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat034_step : block011_data_flat034 = (CoefficientMerge.fastMerge block011_data_flat032 block011_data_flat033) := by decide +kernel
theorem block011_data_flat034_original : block011_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)) := by
  rw [block011_data_flat034_step, block011_data_flat032_original, block011_data_flat033_original]
def block011_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat035_step : block011_data_flat035 = (CoefficientMerge.fastMerge block011_data_flat031 block011_data_flat034) := by decide +kernel
theorem block011_data_flat035_original : block011_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded))) := by
  rw [block011_data_flat035_step, block011_data_flat031_original, block011_data_flat034_original]
def block011_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat036_step : block011_data_flat036 = (CoefficientMerge.fastMerge block011_data_flat030 block011_data_flat035) := by decide +kernel
theorem block011_data_flat036_original : block011_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))) := by
  rw [block011_data_flat036_step, block011_data_flat030_original, block011_data_flat035_original]
def block011_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat037_step : block011_data_flat037 = (CoefficientMerge.fastMerge block011_data_flat027 block011_data_flat036) := by decide +kernel
theorem block011_data_flat037_original : block011_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded))))) := by
  rw [block011_data_flat037_step, block011_data_flat027_original, block011_data_flat036_original]
def block011_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680)), (nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680))]
theorem block011_data_flat038_step : block011_data_flat038 = (CoefficientMerge.fastMerge block011_data_flat018 block011_data_flat037) := by decide +kernel
theorem block011_data_flat038_original : block011_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))))) := by
  rw [block011_data_flat038_step, block011_data_flat018_original, block011_data_flat037_original]
def block011_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 382258800))]
theorem block011_data_flat039_step : block011_data_flat039 = (CoefficientMerge.scale (382258800 : Int) atom0835Coded) := by decide +kernel
theorem block011_data_flat039_original : block011_data_flat039 = (CoefficientMerge.scale (382258800 : Int) atom0835Coded) := by
  rw [block011_data_flat039_step]
def block011_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2077, Int.ofNat (nat_lit 180362880))]
theorem block011_data_flat040_step : block011_data_flat040 = (CoefficientMerge.scale (180362880 : Int) atom0836Coded) := by decide +kernel
theorem block011_data_flat040_original : block011_data_flat040 = (CoefficientMerge.scale (180362880 : Int) atom0836Coded) := by
  rw [block011_data_flat040_step]
def block011_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880))]
theorem block011_data_flat041_step : block011_data_flat041 = (CoefficientMerge.fastMerge block011_data_flat039 block011_data_flat040) := by decide +kernel
theorem block011_data_flat041_original : block011_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) := by
  rw [block011_data_flat041_step, block011_data_flat039_original, block011_data_flat040_original]
def block011_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2080, Int.ofNat (nat_lit 103864320))]
theorem block011_data_flat042_step : block011_data_flat042 = (CoefficientMerge.scale (103864320 : Int) atom0837Coded) := by decide +kernel
theorem block011_data_flat042_original : block011_data_flat042 = (CoefficientMerge.scale (103864320 : Int) atom0837Coded) := by
  rw [block011_data_flat042_step]
def block011_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 207728640))]
theorem block011_data_flat043_step : block011_data_flat043 = (CoefficientMerge.scale (207728640 : Int) atom0838Coded) := by decide +kernel
theorem block011_data_flat043_original : block011_data_flat043 = (CoefficientMerge.scale (207728640 : Int) atom0838Coded) := by
  rw [block011_data_flat043_step]
def block011_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2082, Int.ofNat (nat_lit 469928592))]
theorem block011_data_flat044_step : block011_data_flat044 = (CoefficientMerge.scale (469928592 : Int) atom0839Coded) := by decide +kernel
theorem block011_data_flat044_original : block011_data_flat044 = (CoefficientMerge.scale (469928592 : Int) atom0839Coded) := by
  rw [block011_data_flat044_step]
def block011_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592))]
theorem block011_data_flat045_step : block011_data_flat045 = (CoefficientMerge.fastMerge block011_data_flat043 block011_data_flat044) := by decide +kernel
theorem block011_data_flat045_original : block011_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)) := by
  rw [block011_data_flat045_step, block011_data_flat043_original, block011_data_flat044_original]
def block011_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592))]
theorem block011_data_flat046_step : block011_data_flat046 = (CoefficientMerge.fastMerge block011_data_flat042 block011_data_flat045) := by decide +kernel
theorem block011_data_flat046_original : block011_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded))) := by
  rw [block011_data_flat046_step, block011_data_flat042_original, block011_data_flat045_original]
def block011_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592))]
theorem block011_data_flat047_step : block011_data_flat047 = (CoefficientMerge.fastMerge block011_data_flat041 block011_data_flat046) := by decide +kernel
theorem block011_data_flat047_original : block011_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) := by
  rw [block011_data_flat047_step, block011_data_flat041_original, block011_data_flat046_original]
def block011_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 1180247040))]
theorem block011_data_flat048_step : block011_data_flat048 = (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) := by decide +kernel
theorem block011_data_flat048_original : block011_data_flat048 = (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) := by
  rw [block011_data_flat048_step]
def block011_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2086, Int.ofNat (nat_lit 2293143552))]
theorem block011_data_flat049_step : block011_data_flat049 = (CoefficientMerge.scale (2293143552 : Int) atom0841Coded) := by decide +kernel
theorem block011_data_flat049_original : block011_data_flat049 = (CoefficientMerge.scale (2293143552 : Int) atom0841Coded) := by
  rw [block011_data_flat049_step]
def block011_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552))]
theorem block011_data_flat050_step : block011_data_flat050 = (CoefficientMerge.fastMerge block011_data_flat048 block011_data_flat049) := by decide +kernel
theorem block011_data_flat050_original : block011_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) := by
  rw [block011_data_flat050_step, block011_data_flat048_original, block011_data_flat049_original]
def block011_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 3586383360))]
theorem block011_data_flat051_step : block011_data_flat051 = (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) := by decide +kernel
theorem block011_data_flat051_original : block011_data_flat051 = (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) := by
  rw [block011_data_flat051_step]
def block011_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 389278080))]
theorem block011_data_flat052_step : block011_data_flat052 = (CoefficientMerge.scale (389278080 : Int) atom0843Coded) := by decide +kernel
theorem block011_data_flat052_original : block011_data_flat052 = (CoefficientMerge.scale (389278080 : Int) atom0843Coded) := by
  rw [block011_data_flat052_step]
def block011_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2097, Int.ofNat (nat_lit 568454400))]
theorem block011_data_flat053_step : block011_data_flat053 = (CoefficientMerge.scale (568454400 : Int) atom0844Coded) := by decide +kernel
theorem block011_data_flat053_original : block011_data_flat053 = (CoefficientMerge.scale (568454400 : Int) atom0844Coded) := by
  rw [block011_data_flat053_step]
def block011_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400))]
theorem block011_data_flat054_step : block011_data_flat054 = (CoefficientMerge.fastMerge block011_data_flat052 block011_data_flat053) := by decide +kernel
theorem block011_data_flat054_original : block011_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded)) := by
  rw [block011_data_flat054_step, block011_data_flat052_original, block011_data_flat053_original]
def block011_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400))]
theorem block011_data_flat055_step : block011_data_flat055 = (CoefficientMerge.fastMerge block011_data_flat051 block011_data_flat054) := by decide +kernel
theorem block011_data_flat055_original : block011_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))) := by
  rw [block011_data_flat055_step, block011_data_flat051_original, block011_data_flat054_original]
def block011_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400))]
theorem block011_data_flat056_step : block011_data_flat056 = (CoefficientMerge.fastMerge block011_data_flat050 block011_data_flat055) := by decide +kernel
theorem block011_data_flat056_original : block011_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded)))) := by
  rw [block011_data_flat056_step, block011_data_flat050_original, block011_data_flat055_original]
def block011_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400))]
theorem block011_data_flat057_step : block011_data_flat057 = (CoefficientMerge.fastMerge block011_data_flat047 block011_data_flat056) := by decide +kernel
theorem block011_data_flat057_original : block011_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) := by
  rw [block011_data_flat057_step, block011_data_flat047_original, block011_data_flat056_original]
def block011_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 725863680))]
theorem block011_data_flat058_step : block011_data_flat058 = (CoefficientMerge.scale (725863680 : Int) atom0845Coded) := by decide +kernel
theorem block011_data_flat058_original : block011_data_flat058 = (CoefficientMerge.scale (725863680 : Int) atom0845Coded) := by
  rw [block011_data_flat058_step]
def block011_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2099, Int.ofNat (nat_lit 883272960))]
theorem block011_data_flat059_step : block011_data_flat059 = (CoefficientMerge.scale (883272960 : Int) atom0846Coded) := by decide +kernel
theorem block011_data_flat059_original : block011_data_flat059 = (CoefficientMerge.scale (883272960 : Int) atom0846Coded) := by
  rw [block011_data_flat059_step]
def block011_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960))]
theorem block011_data_flat060_step : block011_data_flat060 = (CoefficientMerge.fastMerge block011_data_flat058 block011_data_flat059) := by decide +kernel
theorem block011_data_flat060_original : block011_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) := by
  rw [block011_data_flat060_step, block011_data_flat058_original, block011_data_flat059_original]
def block011_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2100, Int.ofNat (nat_lit 757621440))]
theorem block011_data_flat061_step : block011_data_flat061 = (CoefficientMerge.scale (757621440 : Int) atom0847Coded) := by decide +kernel
theorem block011_data_flat061_original : block011_data_flat061 = (CoefficientMerge.scale (757621440 : Int) atom0847Coded) := by
  rw [block011_data_flat061_step]
def block011_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2101, Int.ofNat (nat_lit 428863920))]
theorem block011_data_flat062_step : block011_data_flat062 = (CoefficientMerge.scale (428863920 : Int) atom0848Coded) := by decide +kernel
theorem block011_data_flat062_original : block011_data_flat062 = (CoefficientMerge.scale (428863920 : Int) atom0848Coded) := by
  rw [block011_data_flat062_step]
def block011_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2102, Int.ofNat (nat_lit 816511200))]
theorem block011_data_flat063_step : block011_data_flat063 = (CoefficientMerge.scale (816511200 : Int) atom0849Coded) := by decide +kernel
theorem block011_data_flat063_original : block011_data_flat063 = (CoefficientMerge.scale (816511200 : Int) atom0849Coded) := by
  rw [block011_data_flat063_step]
def block011_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200))]
theorem block011_data_flat064_step : block011_data_flat064 = (CoefficientMerge.fastMerge block011_data_flat062 block011_data_flat063) := by decide +kernel
theorem block011_data_flat064_original : block011_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)) := by
  rw [block011_data_flat064_step, block011_data_flat062_original, block011_data_flat063_original]
def block011_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200))]
theorem block011_data_flat065_step : block011_data_flat065 = (CoefficientMerge.fastMerge block011_data_flat061 block011_data_flat064) := by decide +kernel
theorem block011_data_flat065_original : block011_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded))) := by
  rw [block011_data_flat065_step, block011_data_flat061_original, block011_data_flat064_original]
def block011_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200))]
theorem block011_data_flat066_step : block011_data_flat066 = (CoefficientMerge.fastMerge block011_data_flat060 block011_data_flat065) := by decide +kernel
theorem block011_data_flat066_original : block011_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) := by
  rw [block011_data_flat066_step, block011_data_flat060_original, block011_data_flat065_original]
def block011_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 2272055280))]
theorem block011_data_flat067_step : block011_data_flat067 = (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) := by decide +kernel
theorem block011_data_flat067_original : block011_data_flat067 = (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) := by
  rw [block011_data_flat067_step]
def block011_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 4061745360))]
theorem block011_data_flat068_step : block011_data_flat068 = (CoefficientMerge.scale (4061745360 : Int) atom0851Coded) := by decide +kernel
theorem block011_data_flat068_original : block011_data_flat068 = (CoefficientMerge.scale (4061745360 : Int) atom0851Coded) := by
  rw [block011_data_flat068_step]
def block011_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360))]
theorem block011_data_flat069_step : block011_data_flat069 = (CoefficientMerge.fastMerge block011_data_flat067 block011_data_flat068) := by decide +kernel
theorem block011_data_flat069_original : block011_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) := by
  rw [block011_data_flat069_step, block011_data_flat067_original, block011_data_flat068_original]
def block011_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2105, Int.ofNat (nat_lit 6158118240))]
theorem block011_data_flat070_step : block011_data_flat070 = (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) := by decide +kernel
theorem block011_data_flat070_original : block011_data_flat070 = (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) := by
  rw [block011_data_flat070_step]
def block011_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2115, Int.ofNat (nat_lit 852681600))]
theorem block011_data_flat071_step : block011_data_flat071 = (CoefficientMerge.scale (852681600 : Int) atom0853Coded) := by decide +kernel
theorem block011_data_flat071_original : block011_data_flat071 = (CoefficientMerge.scale (852681600 : Int) atom0853Coded) := by
  rw [block011_data_flat071_step]
def block011_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat072_step : block011_data_flat072 = (CoefficientMerge.scale (1515283200 : Int) atom0854Coded) := by decide +kernel
theorem block011_data_flat072_original : block011_data_flat072 = (CoefficientMerge.scale (1515283200 : Int) atom0854Coded) := by
  rw [block011_data_flat072_step]
def block011_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat073_step : block011_data_flat073 = (CoefficientMerge.fastMerge block011_data_flat071 block011_data_flat072) := by decide +kernel
theorem block011_data_flat073_original : block011_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded)) := by
  rw [block011_data_flat073_step, block011_data_flat071_original, block011_data_flat072_original]
def block011_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat074_step : block011_data_flat074 = (CoefficientMerge.fastMerge block011_data_flat070 block011_data_flat073) := by decide +kernel
theorem block011_data_flat074_original : block011_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))) := by
  rw [block011_data_flat074_step, block011_data_flat070_original, block011_data_flat073_original]
def block011_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat075_step : block011_data_flat075 = (CoefficientMerge.fastMerge block011_data_flat069 block011_data_flat074) := by decide +kernel
theorem block011_data_flat075_original : block011_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded)))) := by
  rw [block011_data_flat075_step, block011_data_flat069_original, block011_data_flat074_original]
def block011_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat076_step : block011_data_flat076 = (CoefficientMerge.fastMerge block011_data_flat066 block011_data_flat075) := by decide +kernel
theorem block011_data_flat076_original : block011_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))))) := by
  rw [block011_data_flat076_step, block011_data_flat066_original, block011_data_flat075_original]
def block011_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400)), (nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat077_step : block011_data_flat077 = (CoefficientMerge.fastMerge block011_data_flat057 block011_data_flat076) := by decide +kernel
theorem block011_data_flat077_original : block011_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded)))))) := by
  rw [block011_data_flat077_step, block011_data_flat057_original, block011_data_flat076_original]
def block011_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680)), (nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680)), (nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400)), (nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200))]
theorem block011_data_flat078_step : block011_data_flat078 = (CoefficientMerge.fastMerge block011_data_flat038 block011_data_flat077) := by decide +kernel
theorem block011_data_flat078_original : block011_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))))))) := by
  rw [block011_data_flat078_step, block011_data_flat038_original, block011_data_flat077_original]
def block011_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080))]
theorem block011_data_flat079_step : block011_data_flat079 = (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) := by decide +kernel
theorem block011_data_flat079_original : block011_data_flat079 = (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) := by
  rw [block011_data_flat079_step]
def block011_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2118, Int.ofNat (nat_lit 1750199040))]
theorem block011_data_flat080_step : block011_data_flat080 = (CoefficientMerge.scale (1750199040 : Int) atom0856Coded) := by decide +kernel
theorem block011_data_flat080_original : block011_data_flat080 = (CoefficientMerge.scale (1750199040 : Int) atom0856Coded) := by
  rw [block011_data_flat080_step]
def block011_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040))]
theorem block011_data_flat081_step : block011_data_flat081 = (CoefficientMerge.fastMerge block011_data_flat079 block011_data_flat080) := by decide +kernel
theorem block011_data_flat081_original : block011_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) := by
  rw [block011_data_flat081_step, block011_data_flat079_original, block011_data_flat080_original]
def block011_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 1645188720))]
theorem block011_data_flat082_step : block011_data_flat082 = (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) := by decide +kernel
theorem block011_data_flat082_original : block011_data_flat082 = (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) := by
  rw [block011_data_flat082_step]
def block011_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2120, Int.ofNat (nat_lit 2642200800))]
theorem block011_data_flat083_step : block011_data_flat083 = (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) := by decide +kernel
theorem block011_data_flat083_original : block011_data_flat083 = (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) := by
  rw [block011_data_flat083_step]
def block011_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2121, Int.ofNat (nat_lit 3897057840))]
theorem block011_data_flat084_step : block011_data_flat084 = (CoefficientMerge.scale (3897057840 : Int) atom0859Coded) := by decide +kernel
theorem block011_data_flat084_original : block011_data_flat084 = (CoefficientMerge.scale (3897057840 : Int) atom0859Coded) := by
  rw [block011_data_flat084_step]
def block011_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840))]
theorem block011_data_flat085_step : block011_data_flat085 = (CoefficientMerge.fastMerge block011_data_flat083 block011_data_flat084) := by decide +kernel
theorem block011_data_flat085_original : block011_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)) := by
  rw [block011_data_flat085_step, block011_data_flat083_original, block011_data_flat084_original]
def block011_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840))]
theorem block011_data_flat086_step : block011_data_flat086 = (CoefficientMerge.fastMerge block011_data_flat082 block011_data_flat085) := by decide +kernel
theorem block011_data_flat086_original : block011_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded))) := by
  rw [block011_data_flat086_step, block011_data_flat082_original, block011_data_flat085_original]
def block011_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840))]
theorem block011_data_flat087_step : block011_data_flat087 = (CoefficientMerge.fastMerge block011_data_flat081 block011_data_flat086) := by decide +kernel
theorem block011_data_flat087_original : block011_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) := by
  rw [block011_data_flat087_step, block011_data_flat081_original, block011_data_flat086_original]
def block011_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2122, Int.ofNat (nat_lit 5871678480))]
theorem block011_data_flat088_step : block011_data_flat088 = (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) := by decide +kernel
theorem block011_data_flat088_original : block011_data_flat088 = (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) := by
  rw [block011_data_flat088_step]
def block011_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2123, Int.ofNat (nat_lit 8109758880))]
theorem block011_data_flat089_step : block011_data_flat089 = (CoefficientMerge.scale (8109758880 : Int) atom0861Coded) := by decide +kernel
theorem block011_data_flat089_original : block011_data_flat089 = (CoefficientMerge.scale (8109758880 : Int) atom0861Coded) := by
  rw [block011_data_flat089_step]
def block011_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880))]
theorem block011_data_flat090_step : block011_data_flat090 = (CoefficientMerge.fastMerge block011_data_flat088 block011_data_flat089) := by decide +kernel
theorem block011_data_flat090_original : block011_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) := by
  rw [block011_data_flat090_step, block011_data_flat088_original, block011_data_flat089_original]
def block011_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2134, Int.ofNat (nat_lit 1439971200))]
theorem block011_data_flat091_step : block011_data_flat091 = (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) := by decide +kernel
theorem block011_data_flat091_original : block011_data_flat091 = (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) := by
  rw [block011_data_flat091_step]
def block011_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 2659495680))]
theorem block011_data_flat092_step : block011_data_flat092 = (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) := by decide +kernel
theorem block011_data_flat092_original : block011_data_flat092 = (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) := by
  rw [block011_data_flat092_step]
def block011_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2136, Int.ofNat (nat_lit 2848556160))]
theorem block011_data_flat093_step : block011_data_flat093 = (CoefficientMerge.scale (2848556160 : Int) atom0864Coded) := by decide +kernel
theorem block011_data_flat093_original : block011_data_flat093 = (CoefficientMerge.scale (2848556160 : Int) atom0864Coded) := by
  rw [block011_data_flat093_step]
def block011_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160))]
theorem block011_data_flat094_step : block011_data_flat094 = (CoefficientMerge.fastMerge block011_data_flat092 block011_data_flat093) := by decide +kernel
theorem block011_data_flat094_original : block011_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded)) := by
  rw [block011_data_flat094_step, block011_data_flat092_original, block011_data_flat093_original]
def block011_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160))]
theorem block011_data_flat095_step : block011_data_flat095 = (CoefficientMerge.fastMerge block011_data_flat091 block011_data_flat094) := by decide +kernel
theorem block011_data_flat095_original : block011_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))) := by
  rw [block011_data_flat095_step, block011_data_flat091_original, block011_data_flat094_original]
def block011_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160))]
theorem block011_data_flat096_step : block011_data_flat096 = (CoefficientMerge.fastMerge block011_data_flat090 block011_data_flat095) := by decide +kernel
theorem block011_data_flat096_original : block011_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded)))) := by
  rw [block011_data_flat096_step, block011_data_flat090_original, block011_data_flat095_original]
def block011_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160))]
theorem block011_data_flat097_step : block011_data_flat097 = (CoefficientMerge.fastMerge block011_data_flat087 block011_data_flat096) := by decide +kernel
theorem block011_data_flat097_original : block011_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) := by
  rw [block011_data_flat097_step, block011_data_flat087_original, block011_data_flat096_original]
def block011_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2137, Int.ofNat (nat_lit 2847306480))]
theorem block011_data_flat098_step : block011_data_flat098 = (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) := by decide +kernel
theorem block011_data_flat098_original : block011_data_flat098 = (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) := by
  rw [block011_data_flat098_step]
def block011_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2138, Int.ofNat (nat_lit 4518209760))]
theorem block011_data_flat099_step : block011_data_flat099 = (CoefficientMerge.scale (4518209760 : Int) atom0866Coded) := by decide +kernel
theorem block011_data_flat099_original : block011_data_flat099 = (CoefficientMerge.scale (4518209760 : Int) atom0866Coded) := by
  rw [block011_data_flat099_step]
def block011_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760))]
theorem block011_data_flat100_step : block011_data_flat100 = (CoefficientMerge.fastMerge block011_data_flat098 block011_data_flat099) := by decide +kernel
theorem block011_data_flat100_original : block011_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) := by
  rw [block011_data_flat100_step, block011_data_flat098_original, block011_data_flat099_original]
def block011_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 5198213040))]
theorem block011_data_flat101_step : block011_data_flat101 = (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) := by decide +kernel
theorem block011_data_flat101_original : block011_data_flat101 = (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) := by
  rw [block011_data_flat101_step]
def block011_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2140, Int.ofNat (nat_lit 7168110480))]
theorem block011_data_flat102_step : block011_data_flat102 = (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) := by decide +kernel
theorem block011_data_flat102_original : block011_data_flat102 = (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) := by
  rw [block011_data_flat102_step]
def block011_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 9649000800))]
theorem block011_data_flat103_step : block011_data_flat103 = (CoefficientMerge.scale (9649000800 : Int) atom0869Coded) := by decide +kernel
theorem block011_data_flat103_original : block011_data_flat103 = (CoefficientMerge.scale (9649000800 : Int) atom0869Coded) := by
  rw [block011_data_flat103_step]
def block011_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800))]
theorem block011_data_flat104_step : block011_data_flat104 = (CoefficientMerge.fastMerge block011_data_flat102 block011_data_flat103) := by decide +kernel
theorem block011_data_flat104_original : block011_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)) := by
  rw [block011_data_flat104_step, block011_data_flat102_original, block011_data_flat103_original]
def block011_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800))]
theorem block011_data_flat105_step : block011_data_flat105 = (CoefficientMerge.fastMerge block011_data_flat101 block011_data_flat104) := by decide +kernel
theorem block011_data_flat105_original : block011_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded))) := by
  rw [block011_data_flat105_step, block011_data_flat101_original, block011_data_flat104_original]
def block011_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800))]
theorem block011_data_flat106_step : block011_data_flat106 = (CoefficientMerge.fastMerge block011_data_flat100 block011_data_flat105) := by decide +kernel
theorem block011_data_flat106_original : block011_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) := by
  rw [block011_data_flat106_step, block011_data_flat100_original, block011_data_flat105_original]
def block011_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 2330513280))]
theorem block011_data_flat107_step : block011_data_flat107 = (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) := by decide +kernel
theorem block011_data_flat107_original : block011_data_flat107 = (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) := by
  rw [block011_data_flat107_step]
def block011_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2154, Int.ofNat (nat_lit 3823796160))]
theorem block011_data_flat108_step : block011_data_flat108 = (CoefficientMerge.scale (3823796160 : Int) atom0871Coded) := by decide +kernel
theorem block011_data_flat108_original : block011_data_flat108 = (CoefficientMerge.scale (3823796160 : Int) atom0871Coded) := by
  rw [block011_data_flat108_step]
def block011_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160))]
theorem block011_data_flat109_step : block011_data_flat109 = (CoefficientMerge.fastMerge block011_data_flat107 block011_data_flat108) := by decide +kernel
theorem block011_data_flat109_original : block011_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) := by
  rw [block011_data_flat109_step, block011_data_flat107_original, block011_data_flat108_original]
def block011_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 3845127600))]
theorem block011_data_flat110_step : block011_data_flat110 = (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) := by decide +kernel
theorem block011_data_flat110_original : block011_data_flat110 = (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) := by
  rw [block011_data_flat110_step]
def block011_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2156, Int.ofNat (nat_lit 6208074720))]
theorem block011_data_flat111_step : block011_data_flat111 = (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) := by decide +kernel
theorem block011_data_flat111_original : block011_data_flat111 = (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) := by
  rw [block011_data_flat111_step]
def block011_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat112_step : block011_data_flat112 = (CoefficientMerge.scale (7191177840 : Int) atom0874Coded) := by decide +kernel
theorem block011_data_flat112_original : block011_data_flat112 = (CoefficientMerge.scale (7191177840 : Int) atom0874Coded) := by
  rw [block011_data_flat112_step]
def block011_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat113_step : block011_data_flat113 = (CoefficientMerge.fastMerge block011_data_flat111 block011_data_flat112) := by decide +kernel
theorem block011_data_flat113_original : block011_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)) := by
  rw [block011_data_flat113_step, block011_data_flat111_original, block011_data_flat112_original]
def block011_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat114_step : block011_data_flat114 = (CoefficientMerge.fastMerge block011_data_flat110 block011_data_flat113) := by decide +kernel
theorem block011_data_flat114_original : block011_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded))) := by
  rw [block011_data_flat114_step, block011_data_flat110_original, block011_data_flat113_original]
def block011_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat115_step : block011_data_flat115 = (CoefficientMerge.fastMerge block011_data_flat109 block011_data_flat114) := by decide +kernel
theorem block011_data_flat115_original : block011_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))) := by
  rw [block011_data_flat115_step, block011_data_flat109_original, block011_data_flat114_original]
def block011_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat116_step : block011_data_flat116 = (CoefficientMerge.fastMerge block011_data_flat106 block011_data_flat115) := by decide +kernel
theorem block011_data_flat116_original : block011_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded))))) := by
  rw [block011_data_flat116_step, block011_data_flat106_original, block011_data_flat115_original]
def block011_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160)), (nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840))]
theorem block011_data_flat117_step : block011_data_flat117 = (CoefficientMerge.fastMerge block011_data_flat097 block011_data_flat116) := by decide +kernel
theorem block011_data_flat117_original : block011_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))))) := by
  rw [block011_data_flat117_step, block011_data_flat097_original, block011_data_flat116_original]
def block011_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 8066673360))]
theorem block011_data_flat118_step : block011_data_flat118 = (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) := by decide +kernel
theorem block011_data_flat118_original : block011_data_flat118 = (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) := by
  rw [block011_data_flat118_step]
def block011_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2159, Int.ofNat (nat_lit 12681810720))]
theorem block011_data_flat119_step : block011_data_flat119 = (CoefficientMerge.scale (12681810720 : Int) atom0876Coded) := by decide +kernel
theorem block011_data_flat119_original : block011_data_flat119 = (CoefficientMerge.scale (12681810720 : Int) atom0876Coded) := by
  rw [block011_data_flat119_step]
def block011_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720))]
theorem block011_data_flat120_step : block011_data_flat120 = (CoefficientMerge.fastMerge block011_data_flat118 block011_data_flat119) := by decide +kernel
theorem block011_data_flat120_original : block011_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) := by
  rw [block011_data_flat120_step, block011_data_flat118_original, block011_data_flat119_original]
def block011_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 3423651840))]
theorem block011_data_flat121_step : block011_data_flat121 = (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) := by decide +kernel
theorem block011_data_flat121_original : block011_data_flat121 = (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) := by
  rw [block011_data_flat121_step]
def block011_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2173, Int.ofNat (nat_lit 6832572120))]
theorem block011_data_flat122_step : block011_data_flat122 = (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) := by decide +kernel
theorem block011_data_flat122_original : block011_data_flat122 = (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) := by
  rw [block011_data_flat122_step]
def block011_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2174, Int.ofNat (nat_lit 12177540000))]
theorem block011_data_flat123_step : block011_data_flat123 = (CoefficientMerge.scale (12177540000 : Int) atom0879Coded) := by decide +kernel
theorem block011_data_flat123_original : block011_data_flat123 = (CoefficientMerge.scale (12177540000 : Int) atom0879Coded) := by
  rw [block011_data_flat123_step]
def block011_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000))]
theorem block011_data_flat124_step : block011_data_flat124 = (CoefficientMerge.fastMerge block011_data_flat122 block011_data_flat123) := by decide +kernel
theorem block011_data_flat124_original : block011_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)) := by
  rw [block011_data_flat124_step, block011_data_flat122_original, block011_data_flat123_original]
def block011_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000))]
theorem block011_data_flat125_step : block011_data_flat125 = (CoefficientMerge.fastMerge block011_data_flat121 block011_data_flat124) := by decide +kernel
theorem block011_data_flat125_original : block011_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded))) := by
  rw [block011_data_flat125_step, block011_data_flat121_original, block011_data_flat124_original]
def block011_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000))]
theorem block011_data_flat126_step : block011_data_flat126 = (CoefficientMerge.fastMerge block011_data_flat120 block011_data_flat125) := by decide +kernel
theorem block011_data_flat126_original : block011_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) := by
  rw [block011_data_flat126_step, block011_data_flat120_original, block011_data_flat125_original]
def block011_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2175, Int.ofNat (nat_lit 12748840200))]
theorem block011_data_flat127_step : block011_data_flat127 = (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) := by decide +kernel
theorem block011_data_flat127_original : block011_data_flat127 = (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) := by
  rw [block011_data_flat127_step]
def block011_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2176, Int.ofNat (nat_lit 9605408040))]
theorem block011_data_flat128_step : block011_data_flat128 = (CoefficientMerge.scale (9605408040 : Int) atom0881Coded) := by decide +kernel
theorem block011_data_flat128_original : block011_data_flat128 = (CoefficientMerge.scale (9605408040 : Int) atom0881Coded) := by
  rw [block011_data_flat128_step]
def block011_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040))]
theorem block011_data_flat129_step : block011_data_flat129 = (CoefficientMerge.fastMerge block011_data_flat127 block011_data_flat128) := by decide +kernel
theorem block011_data_flat129_original : block011_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) := by
  rw [block011_data_flat129_step, block011_data_flat127_original, block011_data_flat128_original]
def block011_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2177, Int.ofNat (nat_lit 15345278280))]
theorem block011_data_flat130_step : block011_data_flat130 = (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) := by decide +kernel
theorem block011_data_flat130_original : block011_data_flat130 = (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) := by
  rw [block011_data_flat130_step]
def block011_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2191, Int.ofNat (nat_lit 2714923008))]
theorem block011_data_flat131_step : block011_data_flat131 = (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) := by decide +kernel
theorem block011_data_flat131_original : block011_data_flat131 = (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) := by
  rw [block011_data_flat131_step]
def block011_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2192, Int.ofNat (nat_lit 9583020000))]
theorem block011_data_flat132_step : block011_data_flat132 = (CoefficientMerge.scale (9583020000 : Int) atom0884Coded) := by decide +kernel
theorem block011_data_flat132_original : block011_data_flat132 = (CoefficientMerge.scale (9583020000 : Int) atom0884Coded) := by
  rw [block011_data_flat132_step]
def block011_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000))]
theorem block011_data_flat133_step : block011_data_flat133 = (CoefficientMerge.fastMerge block011_data_flat131 block011_data_flat132) := by decide +kernel
theorem block011_data_flat133_original : block011_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded)) := by
  rw [block011_data_flat133_step, block011_data_flat131_original, block011_data_flat132_original]
def block011_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000))]
theorem block011_data_flat134_step : block011_data_flat134 = (CoefficientMerge.fastMerge block011_data_flat130 block011_data_flat133) := by decide +kernel
theorem block011_data_flat134_original : block011_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))) := by
  rw [block011_data_flat134_step, block011_data_flat130_original, block011_data_flat133_original]
def block011_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000))]
theorem block011_data_flat135_step : block011_data_flat135 = (CoefficientMerge.fastMerge block011_data_flat129 block011_data_flat134) := by decide +kernel
theorem block011_data_flat135_original : block011_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded)))) := by
  rw [block011_data_flat135_step, block011_data_flat129_original, block011_data_flat134_original]
def block011_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000))]
theorem block011_data_flat136_step : block011_data_flat136 = (CoefficientMerge.fastMerge block011_data_flat126 block011_data_flat135) := by decide +kernel
theorem block011_data_flat136_original : block011_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) := by
  rw [block011_data_flat136_step, block011_data_flat126_original, block011_data_flat135_original]
def block011_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2193, Int.ofNat (nat_lit 10709800380))]
theorem block011_data_flat137_step : block011_data_flat137 = (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) := by decide +kernel
theorem block011_data_flat137_original : block011_data_flat137 = (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) := by
  rw [block011_data_flat137_step]
def block011_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2194, Int.ofNat (nat_lit 8121848400))]
theorem block011_data_flat138_step : block011_data_flat138 = (CoefficientMerge.scale (8121848400 : Int) atom0886Coded) := by decide +kernel
theorem block011_data_flat138_original : block011_data_flat138 = (CoefficientMerge.scale (8121848400 : Int) atom0886Coded) := by
  rw [block011_data_flat138_step]
def block011_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400))]
theorem block011_data_flat139_step : block011_data_flat139 = (CoefficientMerge.fastMerge block011_data_flat137 block011_data_flat138) := by decide +kernel
theorem block011_data_flat139_original : block011_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) := by
  rw [block011_data_flat139_step, block011_data_flat137_original, block011_data_flat138_original]
def block011_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2195, Int.ofNat (nat_lit 11055343770))]
theorem block011_data_flat140_step : block011_data_flat140 = (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) := by decide +kernel
theorem block011_data_flat140_original : block011_data_flat140 = (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) := by
  rw [block011_data_flat140_step]
def block011_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2210, Int.ofNat (nat_lit 7705827000))]
theorem block011_data_flat141_step : block011_data_flat141 = (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) := by decide +kernel
theorem block011_data_flat141_original : block011_data_flat141 = (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) := by
  rw [block011_data_flat141_step]
def block011_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2211, Int.ofNat (nat_lit 12583600560))]
theorem block011_data_flat142_step : block011_data_flat142 = (CoefficientMerge.scale (12583600560 : Int) atom0889Coded) := by decide +kernel
theorem block011_data_flat142_original : block011_data_flat142 = (CoefficientMerge.scale (12583600560 : Int) atom0889Coded) := by
  rw [block011_data_flat142_step]
def block011_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560))]
theorem block011_data_flat143_step : block011_data_flat143 = (CoefficientMerge.fastMerge block011_data_flat141 block011_data_flat142) := by decide +kernel
theorem block011_data_flat143_original : block011_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)) := by
  rw [block011_data_flat143_step, block011_data_flat141_original, block011_data_flat142_original]
def block011_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560))]
theorem block011_data_flat144_step : block011_data_flat144 = (CoefficientMerge.fastMerge block011_data_flat140 block011_data_flat143) := by decide +kernel
theorem block011_data_flat144_original : block011_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded))) := by
  rw [block011_data_flat144_step, block011_data_flat140_original, block011_data_flat143_original]
def block011_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560))]
theorem block011_data_flat145_step : block011_data_flat145 = (CoefficientMerge.fastMerge block011_data_flat139 block011_data_flat144) := by decide +kernel
theorem block011_data_flat145_original : block011_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) := by
  rw [block011_data_flat145_step, block011_data_flat139_original, block011_data_flat144_original]
def block011_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2212, Int.ofNat (nat_lit 9594135720))]
theorem block011_data_flat146_step : block011_data_flat146 = (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) := by decide +kernel
theorem block011_data_flat146_original : block011_data_flat146 = (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) := by
  rw [block011_data_flat146_step]
def block011_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2213, Int.ofNat (nat_lit 13657509000))]
theorem block011_data_flat147_step : block011_data_flat147 = (CoefficientMerge.scale (13657509000 : Int) atom0891Coded) := by decide +kernel
theorem block011_data_flat147_original : block011_data_flat147 = (CoefficientMerge.scale (13657509000 : Int) atom0891Coded) := by
  rw [block011_data_flat147_step]
def block011_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000))]
theorem block011_data_flat148_step : block011_data_flat148 = (CoefficientMerge.fastMerge block011_data_flat146 block011_data_flat147) := by decide +kernel
theorem block011_data_flat148_original : block011_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) := by
  rw [block011_data_flat148_step, block011_data_flat146_original, block011_data_flat147_original]
def block011_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2229, Int.ofNat (nat_lit 3582383220))]
theorem block011_data_flat149_step : block011_data_flat149 = (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) := by decide +kernel
theorem block011_data_flat149_original : block011_data_flat149 = (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) := by
  rw [block011_data_flat149_step]
def block011_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2230, Int.ofNat (nat_lit 5086811700))]
theorem block011_data_flat150_step : block011_data_flat150 = (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) := by decide +kernel
theorem block011_data_flat150_original : block011_data_flat150 = (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) := by
  rw [block011_data_flat150_step]
def block011_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat151_step : block011_data_flat151 = (CoefficientMerge.scale (9511338690 : Int) atom0894Coded) := by decide +kernel
theorem block011_data_flat151_original : block011_data_flat151 = (CoefficientMerge.scale (9511338690 : Int) atom0894Coded) := by
  rw [block011_data_flat151_step]
def block011_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat152_step : block011_data_flat152 = (CoefficientMerge.fastMerge block011_data_flat150 block011_data_flat151) := by decide +kernel
theorem block011_data_flat152_original : block011_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded)) := by
  rw [block011_data_flat152_step, block011_data_flat150_original, block011_data_flat151_original]
def block011_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat153_step : block011_data_flat153 = (CoefficientMerge.fastMerge block011_data_flat149 block011_data_flat152) := by decide +kernel
theorem block011_data_flat153_original : block011_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded))) := by
  rw [block011_data_flat153_step, block011_data_flat149_original, block011_data_flat152_original]
def block011_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat154_step : block011_data_flat154 = (CoefficientMerge.fastMerge block011_data_flat148 block011_data_flat153) := by decide +kernel
theorem block011_data_flat154_original : block011_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded)))) := by
  rw [block011_data_flat154_step, block011_data_flat148_original, block011_data_flat153_original]
def block011_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat155_step : block011_data_flat155 = (CoefficientMerge.fastMerge block011_data_flat145 block011_data_flat154) := by decide +kernel
theorem block011_data_flat155_original : block011_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded))))) := by
  rw [block011_data_flat155_step, block011_data_flat145_original, block011_data_flat154_original]
def block011_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000)), (nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat156_step : block011_data_flat156 = (CoefficientMerge.fastMerge block011_data_flat136 block011_data_flat155) := by decide +kernel
theorem block011_data_flat156_original : block011_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded)))))) := by
  rw [block011_data_flat156_step, block011_data_flat136_original, block011_data_flat155_original]
def block011_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160)), (nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840)), (nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000)), (nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat157_step : block011_data_flat157 = (CoefficientMerge.fastMerge block011_data_flat117 block011_data_flat156) := by decide +kernel
theorem block011_data_flat157_original : block011_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded))))))) := by
  rw [block011_data_flat157_step, block011_data_flat117_original, block011_data_flat156_original]
def block011_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680)), (nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680)), (nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400)), (nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200)), (nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160)), (nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840)), (nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000)), (nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat158_step : block011_data_flat158 = (CoefficientMerge.fastMerge block011_data_flat078 block011_data_flat157) := by decide +kernel
theorem block011_data_flat158_original : block011_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded)))))))) := by
  rw [block011_data_flat158_step, block011_data_flat078_original, block011_data_flat157_original]
def block011_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1851, Int.ofNat (nat_lit 13013137800)), (nat_lit 1852, Int.ofNat (nat_lit 9515050920)), (nat_lit 1853, Int.ofNat (nat_lit 14900266440)), (nat_lit 1867, Int.ofNat (nat_lit 3202633728)), (nat_lit 1868, Int.ofNat (nat_lit 10330996320)), (nat_lit 1869, Int.ofNat (nat_lit 11120842620)), (nat_lit 1870, Int.ofNat (nat_lit 8447358000)), (nat_lit 1871, Int.ofNat (nat_lit 10737773370)), (nat_lit 1886, Int.ofNat (nat_lit 7850979000)), (nat_lit 1887, Int.ofNat (nat_lit 12484453680)), (nat_lit 1888, Int.ofNat (nat_lit 9208198920)), (nat_lit 1889, Int.ofNat (nat_lit 12481979400)), (nat_lit 1905, Int.ofNat (nat_lit 3495594420)), (nat_lit 1906, Int.ofNat (nat_lit 4734746820)), (nat_lit 1907, Int.ofNat (nat_lit 8199759330)), (nat_lit 1925, Int.ofNat (nat_lit 3354207030)), (nat_lit 1943, Int.ofNat (nat_lit 3244305150)), (nat_lit 2058, Int.ofNat (nat_lit 199002240)), (nat_lit 2059, Int.ofNat (nat_lit 103864320)), (nat_lit 2060, Int.ofNat (nat_lit 25159680)), (nat_lit 2064, Int.ofNat (nat_lit 382258800)), (nat_lit 2077, Int.ofNat (nat_lit 180362880)), (nat_lit 2080, Int.ofNat (nat_lit 103864320)), (nat_lit 2081, Int.ofNat (nat_lit 207728640)), (nat_lit 2082, Int.ofNat (nat_lit 469928592)), (nat_lit 2085, Int.ofNat (nat_lit 1180247040)), (nat_lit 2086, Int.ofNat (nat_lit 2293143552)), (nat_lit 2087, Int.ofNat (nat_lit 3586383360)), (nat_lit 2096, Int.ofNat (nat_lit 389278080)), (nat_lit 2097, Int.ofNat (nat_lit 568454400)), (nat_lit 2098, Int.ofNat (nat_lit 725863680)), (nat_lit 2099, Int.ofNat (nat_lit 883272960)), (nat_lit 2100, Int.ofNat (nat_lit 757621440)), (nat_lit 2101, Int.ofNat (nat_lit 428863920)), (nat_lit 2102, Int.ofNat (nat_lit 816511200)), (nat_lit 2103, Int.ofNat (nat_lit 2272055280)), (nat_lit 2104, Int.ofNat (nat_lit 4061745360)), (nat_lit 2105, Int.ofNat (nat_lit 6158118240)), (nat_lit 2115, Int.ofNat (nat_lit 852681600)), (nat_lit 2116, Int.ofNat (nat_lit 1515283200)), (nat_lit 2117, Int.ofNat (nat_lit 1675918080)), (nat_lit 2118, Int.ofNat (nat_lit 1750199040)), (nat_lit 2119, Int.ofNat (nat_lit 1645188720)), (nat_lit 2120, Int.ofNat (nat_lit 2642200800)), (nat_lit 2121, Int.ofNat (nat_lit 3897057840)), (nat_lit 2122, Int.ofNat (nat_lit 5871678480)), (nat_lit 2123, Int.ofNat (nat_lit 8109758880)), (nat_lit 2134, Int.ofNat (nat_lit 1439971200)), (nat_lit 2135, Int.ofNat (nat_lit 2659495680)), (nat_lit 2136, Int.ofNat (nat_lit 2848556160)), (nat_lit 2137, Int.ofNat (nat_lit 2847306480)), (nat_lit 2138, Int.ofNat (nat_lit 4518209760)), (nat_lit 2139, Int.ofNat (nat_lit 5198213040)), (nat_lit 2140, Int.ofNat (nat_lit 7168110480)), (nat_lit 2141, Int.ofNat (nat_lit 9649000800)), (nat_lit 2153, Int.ofNat (nat_lit 2330513280)), (nat_lit 2154, Int.ofNat (nat_lit 3823796160)), (nat_lit 2155, Int.ofNat (nat_lit 3845127600)), (nat_lit 2156, Int.ofNat (nat_lit 6208074720)), (nat_lit 2157, Int.ofNat (nat_lit 7191177840)), (nat_lit 2158, Int.ofNat (nat_lit 8066673360)), (nat_lit 2159, Int.ofNat (nat_lit 12681810720)), (nat_lit 2172, Int.ofNat (nat_lit 3423651840)), (nat_lit 2173, Int.ofNat (nat_lit 6832572120)), (nat_lit 2174, Int.ofNat (nat_lit 12177540000)), (nat_lit 2175, Int.ofNat (nat_lit 12748840200)), (nat_lit 2176, Int.ofNat (nat_lit 9605408040)), (nat_lit 2177, Int.ofNat (nat_lit 15345278280)), (nat_lit 2191, Int.ofNat (nat_lit 2714923008)), (nat_lit 2192, Int.ofNat (nat_lit 9583020000)), (nat_lit 2193, Int.ofNat (nat_lit 10709800380)), (nat_lit 2194, Int.ofNat (nat_lit 8121848400)), (nat_lit 2195, Int.ofNat (nat_lit 11055343770)), (nat_lit 2210, Int.ofNat (nat_lit 7705827000)), (nat_lit 2211, Int.ofNat (nat_lit 12583600560)), (nat_lit 2212, Int.ofNat (nat_lit 9594135720)), (nat_lit 2213, Int.ofNat (nat_lit 13657509000)), (nat_lit 2229, Int.ofNat (nat_lit 3582383220)), (nat_lit 2230, Int.ofNat (nat_lit 5086811700)), (nat_lit 2231, Int.ofNat (nat_lit 9511338690))]
theorem block011_data_flat159_step : block011_data_flat159 = (CoefficientMerge.trim block011_data_flat158) := by decide +kernel
theorem block011_data_flat159_original : block011_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded))))))))) := by
  rw [block011_data_flat159_step, block011_data_flat158_original]
theorem block011_data : block011 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13013137800 : Int) atom0815Coded) (CoefficientMerge.scale (9515050920 : Int) atom0816Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14900266440 : Int) atom0817Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3202633728 : Int) atom0818Coded) (CoefficientMerge.scale (10330996320 : Int) atom0819Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120842620 : Int) atom0820Coded) (CoefficientMerge.scale (8447358000 : Int) atom0821Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10737773370 : Int) atom0822Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850979000 : Int) atom0823Coded) (CoefficientMerge.scale (12484453680 : Int) atom0824Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9208198920 : Int) atom0825Coded) (CoefficientMerge.scale (12481979400 : Int) atom0826Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3495594420 : Int) atom0827Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4734746820 : Int) atom0828Coded) (CoefficientMerge.scale (8199759330 : Int) atom0829Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3354207030 : Int) atom0830Coded) (CoefficientMerge.scale (3244305150 : Int) atom0831Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199002240 : Int) atom0832Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0833Coded) (CoefficientMerge.scale (25159680 : Int) atom0834Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (382258800 : Int) atom0835Coded) (CoefficientMerge.scale (180362880 : Int) atom0836Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0837Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0838Coded) (CoefficientMerge.scale (469928592 : Int) atom0839Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0840Coded) (CoefficientMerge.scale (2293143552 : Int) atom0841Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0842Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389278080 : Int) atom0843Coded) (CoefficientMerge.scale (568454400 : Int) atom0844Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (725863680 : Int) atom0845Coded) (CoefficientMerge.scale (883272960 : Int) atom0846Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (757621440 : Int) atom0847Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428863920 : Int) atom0848Coded) (CoefficientMerge.scale (816511200 : Int) atom0849Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2272055280 : Int) atom0850Coded) (CoefficientMerge.scale (4061745360 : Int) atom0851Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6158118240 : Int) atom0852Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (852681600 : Int) atom0853Coded) (CoefficientMerge.scale (1515283200 : Int) atom0854Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1675918080 : Int) atom0855Coded) (CoefficientMerge.scale (1750199040 : Int) atom0856Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1645188720 : Int) atom0857Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2642200800 : Int) atom0858Coded) (CoefficientMerge.scale (3897057840 : Int) atom0859Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5871678480 : Int) atom0860Coded) (CoefficientMerge.scale (8109758880 : Int) atom0861Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1439971200 : Int) atom0862Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2659495680 : Int) atom0863Coded) (CoefficientMerge.scale (2848556160 : Int) atom0864Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2847306480 : Int) atom0865Coded) (CoefficientMerge.scale (4518209760 : Int) atom0866Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5198213040 : Int) atom0867Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7168110480 : Int) atom0868Coded) (CoefficientMerge.scale (9649000800 : Int) atom0869Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2330513280 : Int) atom0870Coded) (CoefficientMerge.scale (3823796160 : Int) atom0871Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3845127600 : Int) atom0872Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6208074720 : Int) atom0873Coded) (CoefficientMerge.scale (7191177840 : Int) atom0874Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8066673360 : Int) atom0875Coded) (CoefficientMerge.scale (12681810720 : Int) atom0876Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3423651840 : Int) atom0877Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6832572120 : Int) atom0878Coded) (CoefficientMerge.scale (12177540000 : Int) atom0879Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12748840200 : Int) atom0880Coded) (CoefficientMerge.scale (9605408040 : Int) atom0881Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15345278280 : Int) atom0882Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2714923008 : Int) atom0883Coded) (CoefficientMerge.scale (9583020000 : Int) atom0884Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10709800380 : Int) atom0885Coded) (CoefficientMerge.scale (8121848400 : Int) atom0886Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11055343770 : Int) atom0887Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7705827000 : Int) atom0888Coded) (CoefficientMerge.scale (12583600560 : Int) atom0889Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9594135720 : Int) atom0890Coded) (CoefficientMerge.scale (13657509000 : Int) atom0891Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3582383220 : Int) atom0892Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086811700 : Int) atom0893Coded) (CoefficientMerge.scale (9511338690 : Int) atom0894Coded)))))))) := by
  have h : block011 = block011_data_flat159 := by decide +kernel
  exact h.trans block011_data_flat159_original
theorem block011_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block011 := by
  rw [block011_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0815Coded_nonneg g hg hA hB) (atom0816Coded_nonneg g hg hA hB)) (add_nonneg (atom0817Coded_nonneg g hg hA hB) (add_nonneg (atom0818Coded_nonneg g hg hA hB) (atom0819Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0820Coded_nonneg g hg hA hB) (atom0821Coded_nonneg g hg hA hB)) (add_nonneg (atom0822Coded_nonneg g hg hA hB) (add_nonneg (atom0823Coded_nonneg g hg hA hB) (atom0824Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0825Coded_nonneg g hg hA hB) (atom0826Coded_nonneg g hg hA hB)) (add_nonneg (atom0827Coded_nonneg g hg hA hB) (add_nonneg (atom0828Coded_nonneg g hg hA hB) (atom0829Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0830Coded_nonneg g hg hA hB) (atom0831Coded_nonneg g hg hA hB)) (add_nonneg (atom0832Coded_nonneg g hg hA hB) (add_nonneg (atom0833Coded_nonneg g hg hA hB) (atom0834Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0835Coded_nonneg g hg hA hB) (atom0836Coded_nonneg g hg hA hB)) (add_nonneg (atom0837Coded_nonneg g hg hA hB) (add_nonneg (atom0838Coded_nonneg g hg hA hB) (atom0839Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0840Coded_nonneg g hg hA hB) (atom0841Coded_nonneg g hg hA hB)) (add_nonneg (atom0842Coded_nonneg g hg hA hB) (add_nonneg (atom0843Coded_nonneg g hg hA hB) (atom0844Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0845Coded_nonneg g hg hA hB) (atom0846Coded_nonneg g hg hA hB)) (add_nonneg (atom0847Coded_nonneg g hg hA hB) (add_nonneg (atom0848Coded_nonneg g hg hA hB) (atom0849Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0850Coded_nonneg g hg hA hB) (atom0851Coded_nonneg g hg hA hB)) (add_nonneg (atom0852Coded_nonneg g hg hA hB) (add_nonneg (atom0853Coded_nonneg g hg hA hB) (atom0854Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0855Coded_nonneg g hg hA hB) (atom0856Coded_nonneg g hg hA hB)) (add_nonneg (atom0857Coded_nonneg g hg hA hB) (add_nonneg (atom0858Coded_nonneg g hg hA hB) (atom0859Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0860Coded_nonneg g hg hA hB) (atom0861Coded_nonneg g hg hA hB)) (add_nonneg (atom0862Coded_nonneg g hg hA hB) (add_nonneg (atom0863Coded_nonneg g hg hA hB) (atom0864Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0865Coded_nonneg g hg hA hB) (atom0866Coded_nonneg g hg hA hB)) (add_nonneg (atom0867Coded_nonneg g hg hA hB) (add_nonneg (atom0868Coded_nonneg g hg hA hB) (atom0869Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0870Coded_nonneg g hg hA hB) (atom0871Coded_nonneg g hg hA hB)) (add_nonneg (atom0872Coded_nonneg g hg hA hB) (add_nonneg (atom0873Coded_nonneg g hg hA hB) (atom0874Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0875Coded_nonneg g hg hA hB) (atom0876Coded_nonneg g hg hA hB)) (add_nonneg (atom0877Coded_nonneg g hg hA hB) (add_nonneg (atom0878Coded_nonneg g hg hA hB) (atom0879Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0880Coded_nonneg g hg hA hB) (atom0881Coded_nonneg g hg hA hB)) (add_nonneg (atom0882Coded_nonneg g hg hA hB) (add_nonneg (atom0883Coded_nonneg g hg hA hB) (atom0884Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0885Coded_nonneg g hg hA hB) (atom0886Coded_nonneg g hg hA hB)) (add_nonneg (atom0887Coded_nonneg g hg hA hB) (add_nonneg (atom0888Coded_nonneg g hg hA hB) (atom0889Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0890Coded_nonneg g hg hA hB) (atom0891Coded_nonneg g hg hA hB)) (add_nonneg (atom0892Coded_nonneg g hg hA hB) (add_nonneg (atom0893Coded_nonneg g hg hA hB) (atom0894Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
