-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0816 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0816 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0816 = ((g 3) * (g 6) * (g 15)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0816_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24718775961600 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0816Coded : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 1))]
theorem atom0816Coded_decode : atom0816 = SparsePolynomial.decodeCubic 21 atom0816Coded := by decide +kernel
theorem atom0816Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) := by
  have h := atom0816_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0816Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0817 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0817 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0817 = ((g 3) * (g 6) * (g 16)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0817_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16729808256000 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817Coded : CoefficientMerge.Poly := [(nat_lit 1465, Int.ofNat (nat_lit 1))]
theorem atom0817Coded_decode : atom0817 = SparsePolynomial.decodeCubic 21 atom0817Coded := by decide +kernel
theorem atom0817Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded) := by
  have h := atom0817_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0817Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0818 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0818 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0818 = ((g 3) * (g 6) * (g 17)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0818_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23887200153600 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818Coded : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 1))]
theorem atom0818Coded_decode : atom0818 = SparsePolynomial.decodeCubic 21 atom0818Coded := by decide +kernel
theorem atom0818Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) := by
  have h := atom0818_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0818Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0819 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0819 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0819 = ((g 3) * (g 6) * (g 18)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0819_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25103061043200 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819Coded : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 1))]
theorem atom0819Coded_decode : atom0819 = SparsePolynomial.decodeCubic 21 atom0819Coded := by decide +kernel
theorem atom0819Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) := by
  have h := atom0819_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0819Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0820 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0820 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0820 = ((g 3) * (g 6) * (g 19)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0820_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30426215500800 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820Coded : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 1))]
theorem atom0820Coded_decode : atom0820 = SparsePolynomial.decodeCubic 21 atom0820Coded := by decide +kernel
theorem atom0820Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded) := by
  have h := atom0820_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0820Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0821 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0821 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0821 = ((g 3) * (g 6) * (g 20)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0821_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35749369958400 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821Coded : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 1))]
theorem atom0821Coded_decode : atom0821 = SparsePolynomial.decodeCubic 21 atom0821Coded := by decide +kernel
theorem atom0821Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) := by
  have h := atom0821_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0821Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0822 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0822 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13525981519104 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822Coded : CoefficientMerge.Poly := [(nat_lit 1477, Int.ofNat (nat_lit 1))]
theorem atom0822Coded_decode : atom0822 = SparsePolynomial.decodeCubic 21 atom0822Coded := by decide +kernel
theorem atom0822Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded) := by
  have h := atom0822_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0822Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0823 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0823 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0823 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0823_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23968533112704 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823Coded : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 1))]
theorem atom0823Coded_decode : atom0823 = SparsePolynomial.decodeCubic 21 atom0823Coded := by decide +kernel
theorem atom0823Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) := by
  have h := atom0823_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0823Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0824 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0824 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0824 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0824_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21615660923904 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824Coded : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 1))]
theorem atom0824Coded_decode : atom0824 = SparsePolynomial.decodeCubic 21 atom0824Coded := by decide +kernel
theorem atom0824Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) := by
  have h := atom0824_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0824Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0825 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0825 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0825 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0825_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21699743848704 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825Coded : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 1))]
theorem atom0825Coded_decode : atom0825 = SparsePolynomial.decodeCubic 21 atom0825Coded := by decide +kernel
theorem atom0825Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded) := by
  have h := atom0825_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0825Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0826 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0826 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0826 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0826_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21730917256704 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826Coded : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 1))]
theorem atom0826Coded_decode : atom0826 = SparsePolynomial.decodeCubic 21 atom0826Coded := by decide +kernel
theorem atom0826Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) := by
  have h := atom0826_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0826Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0827 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0827 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0827 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0827_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19796620450304 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827Coded : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 1))]
theorem atom0827Coded_decode : atom0827 = SparsePolynomial.decodeCubic 21 atom0827Coded := by decide +kernel
theorem atom0827Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded) := by
  have h := atom0827_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0827Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0828 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0828 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0828 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0828_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19605402491904 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828Coded : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 1))]
theorem atom0828Coded_decode : atom0828 = SparsePolynomial.decodeCubic 21 atom0828Coded := by decide +kernel
theorem atom0828Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) := by
  have h := atom0828_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0828Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0829 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0829 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0829 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0829_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20291596475904 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829Coded : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 1))]
theorem atom0829Coded_decode : atom0829 = SparsePolynomial.decodeCubic 21 atom0829Coded := by decide +kernel
theorem atom0829Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) := by
  have h := atom0829_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0829Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0830 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0830 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0830 = ((g 3) * (g 7) * (g 15)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0830_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30208777521408 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830Coded : CoefficientMerge.Poly := [(nat_lit 1485, Int.ofNat (nat_lit 1))]
theorem atom0830Coded_decode : atom0830 = SparsePolynomial.decodeCubic 21 atom0830Coded := by decide +kernel
theorem atom0830Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded) := by
  have h := atom0830_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0830Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0831 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0831 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0831 = ((g 3) * (g 7) * (g 16)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0831_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22810615971840 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831Coded : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 1))]
theorem atom0831Coded_decode : atom0831 = SparsePolynomial.decodeCubic 21 atom0831Coded := by decide +kernel
theorem atom0831Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) := by
  have h := atom0831_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0831Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0832 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0832 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0832 = ((g 3) * (g 7) * (g 17)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0832_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30722528510208 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832Coded : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 1))]
theorem atom0832Coded_decode : atom0832 = SparsePolynomial.decodeCubic 21 atom0832Coded := by decide +kernel
theorem atom0832Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded) := by
  have h := atom0832_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0832Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0833 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0833 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0833 = ((g 3) * (g 7) * (g 18)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0833_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30744200282112 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833Coded : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 1))]
theorem atom0833Coded_decode : atom0833 = SparsePolynomial.decodeCubic 21 atom0833Coded := by decide +kernel
theorem atom0833Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) := by
  have h := atom0833_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0833Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0834 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0834 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0834 = ((g 3) * (g 7) * (g 19)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0834_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35800014965760 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834Coded : CoefficientMerge.Poly := [(nat_lit 1489, Int.ofNat (nat_lit 1))]
theorem atom0834Coded_decode : atom0834 = SparsePolynomial.decodeCubic 21 atom0834Coded := by decide +kernel
theorem atom0834Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) := by
  have h := atom0834_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0834Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0835 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0835 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0835 = ((g 3) * (g 7) * (g 20)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0835_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40855829649408 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835Coded : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 1))]
theorem atom0835Coded_decode : atom0835 = SparsePolynomial.decodeCubic 21 atom0835Coded := by decide +kernel
theorem atom0835Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded) := by
  have h := atom0835_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0835Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0836 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0836 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15309696528000 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836Coded : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 1))]
theorem atom0836Coded_decode : atom0836 = SparsePolynomial.decodeCubic 21 atom0836Coded := by decide +kernel
theorem atom0836Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) := by
  have h := atom0836_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0836Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0837 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0837 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0837 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0837_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28111885603200 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837Coded : CoefficientMerge.Poly := [(nat_lit 1500, Int.ofNat (nat_lit 1))]
theorem atom0837Coded_decode : atom0837 = SparsePolynomial.decodeCubic 21 atom0837Coded := by decide +kernel
theorem atom0837Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded) := by
  have h := atom0837_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0837Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0838 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0838 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0838 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0838_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27691470979200 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838Coded : CoefficientMerge.Poly := [(nat_lit 1501, Int.ofNat (nat_lit 1))]
theorem atom0838Coded_decode : atom0838 = SparsePolynomial.decodeCubic 21 atom0838Coded := by decide +kernel
theorem atom0838Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) := by
  have h := atom0838_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0838Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0839 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0839 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0839 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0839_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27218146838400 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839Coded : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 1))]
theorem atom0839Coded_decode : atom0839 = SparsePolynomial.decodeCubic 21 atom0839Coded := by decide +kernel
theorem atom0839Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) := by
  have h := atom0839_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0839Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0840 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0840 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0840 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0840_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24611186633600 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840Coded : CoefficientMerge.Poly := [(nat_lit 1503, Int.ofNat (nat_lit 1))]
theorem atom0840Coded_decode : atom0840 = SparsePolynomial.decodeCubic 21 atom0840Coded := by decide +kernel
theorem atom0840Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded) := by
  have h := atom0840_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0840Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0841 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0841 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0841 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0841_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24174485193600 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841Coded : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 1))]
theorem atom0841Coded_decode : atom0841 = SparsePolynomial.decodeCubic 21 atom0841Coded := by decide +kernel
theorem atom0841Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) := by
  have h := atom0841_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0841Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0842 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0842 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0842 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0842_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24615195696000 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842Coded : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 1))]
theorem atom0842Coded_decode : atom0842 = SparsePolynomial.decodeCubic 21 atom0842Coded := by decide +kernel
theorem atom0842Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded) := by
  have h := atom0842_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0842Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0843 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0843 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0843 = ((g 3) * (g 8) * (g 15)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0843_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33795536947200 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843Coded : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 1))]
theorem atom0843Coded_decode : atom0843 = SparsePolynomial.decodeCubic 21 atom0843Coded := by decide +kernel
theorem atom0843Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) := by
  have h := atom0843_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0843Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0844 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0844 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0844 = ((g 3) * (g 8) * (g 16)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0844_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27092078118000 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844Coded : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 1))]
theorem atom0844Coded_decode : atom0844 = SparsePolynomial.decodeCubic 21 atom0844Coded := by decide +kernel
theorem atom0844Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) := by
  have h := atom0844_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0844Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0845 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0845 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0845 = ((g 3) * (g 8) * (g 17)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0845_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35654614732800 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845Coded : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 1))]
theorem atom0845Coded_decode : atom0845 = SparsePolynomial.decodeCubic 21 atom0845Coded := by decide +kernel
theorem atom0845Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded) := by
  have h := atom0845_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0845Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0846 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0846 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0846 = ((g 3) * (g 8) * (g 18)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0846_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35432355243600 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846Coded : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 1))]
theorem atom0846Coded_decode : atom0846 = SparsePolynomial.decodeCubic 21 atom0846Coded := by decide +kernel
theorem atom0846Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) := by
  have h := atom0846_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0846Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0847 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0847 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0847 = ((g 3) * (g 8) * (g 19)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0847_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40841126298000 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847Coded : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 1))]
theorem atom0847Coded_decode : atom0847 = SparsePolynomial.decodeCubic 21 atom0847Coded := by decide +kernel
theorem atom0847Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded) := by
  have h := atom0847_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0847Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0848 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0848 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0848 = ((g 3) * (g 8) * (g 20)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0848_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46249897352400 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848Coded : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 1))]
theorem atom0848Coded_decode : atom0848 = SparsePolynomial.decodeCubic 21 atom0848Coded := by decide +kernel
theorem atom0848Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) := by
  have h := atom0848_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0848Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0849 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0849 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17669334009600 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849Coded : CoefficientMerge.Poly := [(nat_lit 1521, Int.ofNat (nat_lit 1))]
theorem atom0849Coded_decode : atom0849 = SparsePolynomial.decodeCubic 21 atom0849Coded := by decide +kernel
theorem atom0849Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) := by
  have h := atom0849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0850 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0850 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32970815539200 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850Coded : CoefficientMerge.Poly := [(nat_lit 1522, Int.ofNat (nat_lit 1))]
theorem atom0850Coded_decode : atom0850 = SparsePolynomial.decodeCubic 21 atom0850Coded := by decide +kernel
theorem atom0850Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded) := by
  have h := atom0850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0851 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0851 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31824828000000 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851Coded : CoefficientMerge.Poly := [(nat_lit 1523, Int.ofNat (nat_lit 1))]
theorem atom0851Coded_decode : atom0851 = SparsePolynomial.decodeCubic 21 atom0851Coded := by decide +kernel
theorem atom0851Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) := by
  have h := atom0851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0852 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0852 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29231398380800 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852Coded : CoefficientMerge.Poly := [(nat_lit 1524, Int.ofNat (nat_lit 1))]
theorem atom0852Coded_decode : atom0852 = SparsePolynomial.decodeCubic 21 atom0852Coded := by decide +kernel
theorem atom0852Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded) := by
  have h := atom0852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0853 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0853 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28381047609600 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853Coded : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 1))]
theorem atom0853Coded_decode : atom0853 = SparsePolynomial.decodeCubic 21 atom0853Coded := by decide +kernel
theorem atom0853Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) := by
  have h := atom0853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0854 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0854 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28408108780800 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854Coded : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 1))]
theorem atom0854Coded_decode : atom0854 = SparsePolynomial.decodeCubic 21 atom0854Coded := by decide +kernel
theorem atom0854Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) := by
  have h := atom0854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0855 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0855 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 3) * (g 9) * (g 15)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37232305689600 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855Coded : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 1))]
theorem atom0855Coded_decode : atom0855 = SparsePolynomial.decodeCubic 21 atom0855Coded := by decide +kernel
theorem atom0855Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded) := by
  have h := atom0855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0856 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0856 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 3) * (g 9) * (g 16)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30526491088800 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856Coded : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 1))]
theorem atom0856Coded_decode : atom0856 = SparsePolynomial.decodeCubic 21 atom0856Coded := by decide +kernel
theorem atom0856Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) := by
  have h := atom0856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0857 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0857 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 3) * (g 9) * (g 17)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40436710272000 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857Coded : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 1))]
theorem atom0857Coded_decode : atom0857 = SparsePolynomial.decodeCubic 21 atom0857Coded := by decide +kernel
theorem atom0857Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded) := by
  have h := atom0857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0858 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0858 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 3) * (g 9) * (g 18)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38977066648800 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858Coded : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 1))]
theorem atom0858Coded_decode : atom0858 = SparsePolynomial.decodeCubic 21 atom0858Coded := by decide +kernel
theorem atom0858Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) := by
  have h := atom0858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0859 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0859 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 3) * (g 9) * (g 19)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44597253103200 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859Coded : CoefficientMerge.Poly := [(nat_lit 1531, Int.ofNat (nat_lit 1))]
theorem atom0859Coded_decode : atom0859 = SparsePolynomial.decodeCubic 21 atom0859Coded := by decide +kernel
theorem atom0859Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) := by
  have h := atom0859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0860 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0860 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 3) * (g 9) * (g 20)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50217439557600 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860Coded : CoefficientMerge.Poly := [(nat_lit 1532, Int.ofNat (nat_lit 1))]
theorem atom0860Coded_decode : atom0860 = SparsePolynomial.decodeCubic 21 atom0860Coded := by decide +kernel
theorem atom0860Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded) := by
  have h := atom0860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0861 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0861 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20168626464000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861Coded : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 1))]
theorem atom0861Coded_decode : atom0861 = SparsePolynomial.decodeCubic 21 atom0861Coded := by decide +kernel
theorem atom0861Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) := by
  have h := atom0861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0862 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0862 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37845938592000 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862Coded : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 1))]
theorem atom0862Coded_decode : atom0862 = SparsePolynomial.decodeCubic 21 atom0862Coded := by decide +kernel
theorem atom0862Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded) := by
  have h := atom0862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0863 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0863 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34243513875200 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863Coded : CoefficientMerge.Poly := [(nat_lit 1545, Int.ofNat (nat_lit 1))]
theorem atom0863Coded_decode : atom0863 = SparsePolynomial.decodeCubic 21 atom0863Coded := by decide +kernel
theorem atom0863Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) := by
  have h := atom0863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0864 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0864 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32811347923200 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864Coded : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 1))]
theorem atom0864Coded_decode : atom0864 = SparsePolynomial.decodeCubic 21 atom0864Coded := by decide +kernel
theorem atom0864Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) := by
  have h := atom0864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0865 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0865 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32256593913600 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865Coded : CoefficientMerge.Poly := [(nat_lit 1547, Int.ofNat (nat_lit 1))]
theorem atom0865Coded_decode : atom0865 = SparsePolynomial.decodeCubic 21 atom0865Coded := by decide +kernel
theorem atom0865Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded) := by
  have h := atom0865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0866 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0866 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 3) * (g 10) * (g 15)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40669074432000 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866Coded : CoefficientMerge.Poly := [(nat_lit 1548, Int.ofNat (nat_lit 1))]
theorem atom0866Coded_decode : atom0866 = SparsePolynomial.decodeCubic 21 atom0866Coded := by decide +kernel
theorem atom0866Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) := by
  have h := atom0866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0867 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0867 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 3) * (g 10) * (g 16)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33480266248800 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867Coded : CoefficientMerge.Poly := [(nat_lit 1549, Int.ofNat (nat_lit 1))]
theorem atom0867Coded_decode : atom0867 = SparsePolynomial.decodeCubic 21 atom0867Coded := by decide +kernel
theorem atom0867Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded) := by
  have h := atom0867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0868 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0868 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 3) * (g 10) * (g 17)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45218805811200 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868Coded : CoefficientMerge.Poly := [(nat_lit 1550, Int.ofNat (nat_lit 1))]
theorem atom0868Coded_decode : atom0868 = SparsePolynomial.decodeCubic 21 atom0868Coded := by decide +kernel
theorem atom0868Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) := by
  have h := atom0868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0869 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0869 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 3) * (g 10) * (g 18)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41305052224800 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869Coded : CoefficientMerge.Poly := [(nat_lit 1551, Int.ofNat (nat_lit 1))]
theorem atom0869Coded_decode : atom0869 = SparsePolynomial.decodeCubic 21 atom0869Coded := by decide +kernel
theorem atom0869Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) := by
  have h := atom0869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0870 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0870 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 3) * (g 10) * (g 19)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46701984016800 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870Coded : CoefficientMerge.Poly := [(nat_lit 1552, Int.ofNat (nat_lit 1))]
theorem atom0870Coded_decode : atom0870 = SparsePolynomial.decodeCubic 21 atom0870Coded := by decide +kernel
theorem atom0870Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded) := by
  have h := atom0870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0871 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0871 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 3) * (g 10) * (g 20)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52098915808800 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871Coded : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 1))]
theorem atom0871Coded_decode : atom0871 = SparsePolynomial.decodeCubic 21 atom0871Coded := by decide +kernel
theorem atom0871Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) := by
  have h := atom0871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0872 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0872 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22544457062400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872Coded : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 1))]
theorem atom0872Coded_decode : atom0872 = SparsePolynomial.decodeCubic 21 atom0872Coded := by decide +kernel
theorem atom0872Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded) := by
  have h := atom0872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0873 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0873 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39286802777600 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873Coded : CoefficientMerge.Poly := [(nat_lit 1566, Int.ofNat (nat_lit 1))]
theorem atom0873Coded_decode : atom0873 = SparsePolynomial.decodeCubic 21 atom0873Coded := by decide +kernel
theorem atom0873Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) := by
  have h := atom0873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0874 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0874 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37104655795200 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874Coded : CoefficientMerge.Poly := [(nat_lit 1567, Int.ofNat (nat_lit 1))]
theorem atom0874Coded_decode : atom0874 = SparsePolynomial.decodeCubic 21 atom0874Coded := by decide +kernel
theorem atom0874Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) := by
  have h := atom0874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0875 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0875 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35799920755200 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875Coded : CoefficientMerge.Poly := [(nat_lit 1568, Int.ofNat (nat_lit 1))]
theorem atom0875Coded_decode : atom0875 = SparsePolynomial.decodeCubic 21 atom0875Coded := by decide +kernel
theorem atom0875Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded) := by
  have h := atom0875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0876 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0876 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 3) * (g 11) * (g 15)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43481996006400 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876Coded : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 1))]
theorem atom0876Coded_decode : atom0876 = SparsePolynomial.decodeCubic 21 atom0876Coded := by decide +kernel
theorem atom0876Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) := by
  have h := atom0876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0877 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0877 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 3) * (g 11) * (g 16)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35727947136000 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877Coded : CoefficientMerge.Poly := [(nat_lit 1570, Int.ofNat (nat_lit 1))]
theorem atom0877Coded_decode : atom0877 = SparsePolynomial.decodeCubic 21 atom0877Coded := by decide +kernel
theorem atom0877Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded) := by
  have h := atom0877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0878 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0878 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 3) * (g 11) * (g 17)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49377054182400 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878Coded : CoefficientMerge.Poly := [(nat_lit 1571, Int.ofNat (nat_lit 1))]
theorem atom0878Coded_decode : atom0878 = SparsePolynomial.decodeCubic 21 atom0878Coded := by decide +kernel
theorem atom0878Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) := by
  have h := atom0878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0879 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0879 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 3) * (g 11) * (g 18)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42461403264000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879Coded : CoefficientMerge.Poly := [(nat_lit 1572, Int.ofNat (nat_lit 1))]
theorem atom0879Coded_decode : atom0879 = SparsePolynomial.decodeCubic 21 atom0879Coded := by decide +kernel
theorem atom0879Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) := by
  have h := atom0879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0880 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0880 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 3) * (g 11) * (g 19)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47380775500800 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880Coded : CoefficientMerge.Poly := [(nat_lit 1573, Int.ofNat (nat_lit 1))]
theorem atom0880Coded_decode : atom0880 = SparsePolynomial.decodeCubic 21 atom0880Coded := by decide +kernel
theorem atom0880Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded) := by
  have h := atom0880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0881 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0881 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 3) * (g 11) * (g 20)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52300147737600 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881Coded : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 1))]
theorem atom0881Coded_decode : atom0881 = SparsePolynomial.decodeCubic 21 atom0881Coded := by decide +kernel
theorem atom0881Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) := by
  have h := atom0881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0882 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0882 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22036670566400 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882Coded : CoefficientMerge.Poly := [(nat_lit 1587, Int.ofNat (nat_lit 1))]
theorem atom0882Coded_decode : atom0882 = SparsePolynomial.decodeCubic 21 atom0882Coded := by decide +kernel
theorem atom0882Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded) := by
  have h := atom0882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0883 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0883 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40545867353600 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883Coded : CoefficientMerge.Poly := [(nat_lit 1588, Int.ofNat (nat_lit 1))]
theorem atom0883Coded_decode : atom0883 = SparsePolynomial.decodeCubic 21 atom0883Coded := by decide +kernel
theorem atom0883Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) := by
  have h := atom0883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0884 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0884 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38322985433600 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884Coded : CoefficientMerge.Poly := [(nat_lit 1589, Int.ofNat (nat_lit 1))]
theorem atom0884Coded_decode : atom0884 = SparsePolynomial.decodeCubic 21 atom0884Coded := by decide +kernel
theorem atom0884Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) := by
  have h := atom0884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0885 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0885 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 3) * (g 12) * (g 15)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42195811302400 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885Coded : CoefficientMerge.Poly := [(nat_lit 1590, Int.ofNat (nat_lit 1))]
theorem atom0885Coded_decode : atom0885 = SparsePolynomial.decodeCubic 21 atom0885Coded := by decide +kernel
theorem atom0885Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded) := by
  have h := atom0885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0886 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0886 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 3) * (g 12) * (g 16)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36822593830400 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886Coded : CoefficientMerge.Poly := [(nat_lit 1591, Int.ofNat (nat_lit 1))]
theorem atom0886Coded_decode : atom0886 = SparsePolynomial.decodeCubic 21 atom0886Coded := by decide +kernel
theorem atom0886Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) := by
  have h := atom0886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0887 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0887 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 3) * (g 12) * (g 17)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49436196275200 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887Coded : CoefficientMerge.Poly := [(nat_lit 1592, Int.ofNat (nat_lit 1))]
theorem atom0887Coded_decode : atom0887 = SparsePolynomial.decodeCubic 21 atom0887Coded := by decide +kernel
theorem atom0887Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded) := by
  have h := atom0887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0888 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0888 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 3) * (g 12) * (g 18)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43193208755200 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888Coded : CoefficientMerge.Poly := [(nat_lit 1593, Int.ofNat (nat_lit 1))]
theorem atom0888Coded_decode : atom0888 = SparsePolynomial.decodeCubic 21 atom0888Coded := by decide +kernel
theorem atom0888Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) := by
  have h := atom0888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0889 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0889 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 3) * (g 12) * (g 19)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47080567475200 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889Coded : CoefficientMerge.Poly := [(nat_lit 1594, Int.ofNat (nat_lit 1))]
theorem atom0889Coded_decode : atom0889 = SparsePolynomial.decodeCubic 21 atom0889Coded := by decide +kernel
theorem atom0889Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) := by
  have h := atom0889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0890 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0890 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 3) * (g 12) * (g 20)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51625627200000 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890Coded : CoefficientMerge.Poly := [(nat_lit 1595, Int.ofNat (nat_lit 1))]
theorem atom0890Coded_decode : atom0890 = SparsePolynomial.decodeCubic 21 atom0890Coded := by decide +kernel
theorem atom0890Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded) := by
  have h := atom0890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0891 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0891 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23512015756800 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891Coded : CoefficientMerge.Poly := [(nat_lit 1609, Int.ofNat (nat_lit 1))]
theorem atom0891Coded_decode : atom0891 = SparsePolynomial.decodeCubic 21 atom0891Coded := by decide +kernel
theorem atom0891Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) := by
  have h := atom0891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0892 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0892 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42544303142400 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892Coded : CoefficientMerge.Poly := [(nat_lit 1610, Int.ofNat (nat_lit 1))]
theorem atom0892Coded_decode : atom0892 = SparsePolynomial.decodeCubic 21 atom0892Coded := by decide +kernel
theorem atom0892Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded) := by
  have h := atom0892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0893 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0893 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 3) * (g 13) * (g 15)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45194813697600 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893Coded : CoefficientMerge.Poly := [(nat_lit 1611, Int.ofNat (nat_lit 1))]
theorem atom0893Coded_decode : atom0893 = SparsePolynomial.decodeCubic 21 atom0893Coded := by decide +kernel
theorem atom0893Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) := by
  have h := atom0893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0894 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0894 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 3) * (g 13) * (g 16)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38463278328000 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894Coded : CoefficientMerge.Poly := [(nat_lit 1612, Int.ofNat (nat_lit 1))]
theorem atom0894Coded_decode : atom0894 = SparsePolynomial.decodeCubic 21 atom0894Coded := by decide +kernel
theorem atom0894Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) := by
  have h := atom0894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0895 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0895 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 3) * (g 13) * (g 17)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52981496064000 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895Coded : CoefficientMerge.Poly := [(nat_lit 1613, Int.ofNat (nat_lit 1))]
theorem atom0895Coded_decode : atom0895 = SparsePolynomial.decodeCubic 21 atom0895Coded := by decide +kernel
theorem atom0895Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded) := by
  have h := atom0895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block012 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704)), (nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408)), (nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800)), (nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600)), (nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600)), (nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200)), (nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400)), (nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
def block012_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600))]
theorem block012_data_flat000_step : block012_data_flat000 = (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) := by decide +kernel
theorem block012_data_flat000_original : block012_data_flat000 = (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) := by
  rw [block012_data_flat000_step]
def block012_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1465, Int.ofNat (nat_lit 16729808256000))]
theorem block012_data_flat001_step : block012_data_flat001 = (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded) := by decide +kernel
theorem block012_data_flat001_original : block012_data_flat001 = (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded) := by
  rw [block012_data_flat001_step]
def block012_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000))]
theorem block012_data_flat002_step : block012_data_flat002 = (CoefficientMerge.fastMerge block012_data_flat000 block012_data_flat001) := by decide +kernel
theorem block012_data_flat002_original : block012_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) := by
  rw [block012_data_flat002_step, block012_data_flat000_original, block012_data_flat001_original]
def block012_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 23887200153600))]
theorem block012_data_flat003_step : block012_data_flat003 = (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) := by decide +kernel
theorem block012_data_flat003_original : block012_data_flat003 = (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) := by
  rw [block012_data_flat003_step]
def block012_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 25103061043200))]
theorem block012_data_flat004_step : block012_data_flat004 = (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) := by decide +kernel
theorem block012_data_flat004_original : block012_data_flat004 = (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) := by
  rw [block012_data_flat004_step]
def block012_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 30426215500800))]
theorem block012_data_flat005_step : block012_data_flat005 = (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded) := by decide +kernel
theorem block012_data_flat005_original : block012_data_flat005 = (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded) := by
  rw [block012_data_flat005_step]
def block012_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800))]
theorem block012_data_flat006_step : block012_data_flat006 = (CoefficientMerge.fastMerge block012_data_flat004 block012_data_flat005) := by decide +kernel
theorem block012_data_flat006_original : block012_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)) := by
  rw [block012_data_flat006_step, block012_data_flat004_original, block012_data_flat005_original]
def block012_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800))]
theorem block012_data_flat007_step : block012_data_flat007 = (CoefficientMerge.fastMerge block012_data_flat003 block012_data_flat006) := by decide +kernel
theorem block012_data_flat007_original : block012_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded))) := by
  rw [block012_data_flat007_step, block012_data_flat003_original, block012_data_flat006_original]
def block012_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800))]
theorem block012_data_flat008_step : block012_data_flat008 = (CoefficientMerge.fastMerge block012_data_flat002 block012_data_flat007) := by decide +kernel
theorem block012_data_flat008_original : block012_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) := by
  rw [block012_data_flat008_step, block012_data_flat002_original, block012_data_flat007_original]
def block012_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 35749369958400))]
theorem block012_data_flat009_step : block012_data_flat009 = (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) := by decide +kernel
theorem block012_data_flat009_original : block012_data_flat009 = (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) := by
  rw [block012_data_flat009_step]
def block012_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1477, Int.ofNat (nat_lit 13525981519104))]
theorem block012_data_flat010_step : block012_data_flat010 = (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded) := by decide +kernel
theorem block012_data_flat010_original : block012_data_flat010 = (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded) := by
  rw [block012_data_flat010_step]
def block012_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104))]
theorem block012_data_flat011_step : block012_data_flat011 = (CoefficientMerge.fastMerge block012_data_flat009 block012_data_flat010) := by decide +kernel
theorem block012_data_flat011_original : block012_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) := by
  rw [block012_data_flat011_step, block012_data_flat009_original, block012_data_flat010_original]
def block012_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 23968533112704))]
theorem block012_data_flat012_step : block012_data_flat012 = (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) := by decide +kernel
theorem block012_data_flat012_original : block012_data_flat012 = (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) := by
  rw [block012_data_flat012_step]
def block012_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 21615660923904))]
theorem block012_data_flat013_step : block012_data_flat013 = (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) := by decide +kernel
theorem block012_data_flat013_original : block012_data_flat013 = (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) := by
  rw [block012_data_flat013_step]
def block012_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 21699743848704))]
theorem block012_data_flat014_step : block012_data_flat014 = (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded) := by decide +kernel
theorem block012_data_flat014_original : block012_data_flat014 = (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded) := by
  rw [block012_data_flat014_step]
def block012_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704))]
theorem block012_data_flat015_step : block012_data_flat015 = (CoefficientMerge.fastMerge block012_data_flat013 block012_data_flat014) := by decide +kernel
theorem block012_data_flat015_original : block012_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded)) := by
  rw [block012_data_flat015_step, block012_data_flat013_original, block012_data_flat014_original]
def block012_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704))]
theorem block012_data_flat016_step : block012_data_flat016 = (CoefficientMerge.fastMerge block012_data_flat012 block012_data_flat015) := by decide +kernel
theorem block012_data_flat016_original : block012_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))) := by
  rw [block012_data_flat016_step, block012_data_flat012_original, block012_data_flat015_original]
def block012_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704))]
theorem block012_data_flat017_step : block012_data_flat017 = (CoefficientMerge.fastMerge block012_data_flat011 block012_data_flat016) := by decide +kernel
theorem block012_data_flat017_original : block012_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded)))) := by
  rw [block012_data_flat017_step, block012_data_flat011_original, block012_data_flat016_original]
def block012_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704))]
theorem block012_data_flat018_step : block012_data_flat018 = (CoefficientMerge.fastMerge block012_data_flat008 block012_data_flat017) := by decide +kernel
theorem block012_data_flat018_original : block012_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) := by
  rw [block012_data_flat018_step, block012_data_flat008_original, block012_data_flat017_original]
def block012_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 21730917256704))]
theorem block012_data_flat019_step : block012_data_flat019 = (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) := by decide +kernel
theorem block012_data_flat019_original : block012_data_flat019 = (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) := by
  rw [block012_data_flat019_step]
def block012_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 19796620450304))]
theorem block012_data_flat020_step : block012_data_flat020 = (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded) := by decide +kernel
theorem block012_data_flat020_original : block012_data_flat020 = (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded) := by
  rw [block012_data_flat020_step]
def block012_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304))]
theorem block012_data_flat021_step : block012_data_flat021 = (CoefficientMerge.fastMerge block012_data_flat019 block012_data_flat020) := by decide +kernel
theorem block012_data_flat021_original : block012_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) := by
  rw [block012_data_flat021_step, block012_data_flat019_original, block012_data_flat020_original]
def block012_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 19605402491904))]
theorem block012_data_flat022_step : block012_data_flat022 = (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) := by decide +kernel
theorem block012_data_flat022_original : block012_data_flat022 = (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) := by
  rw [block012_data_flat022_step]
def block012_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 20291596475904))]
theorem block012_data_flat023_step : block012_data_flat023 = (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) := by decide +kernel
theorem block012_data_flat023_original : block012_data_flat023 = (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) := by
  rw [block012_data_flat023_step]
def block012_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1485, Int.ofNat (nat_lit 30208777521408))]
theorem block012_data_flat024_step : block012_data_flat024 = (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded) := by decide +kernel
theorem block012_data_flat024_original : block012_data_flat024 = (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded) := by
  rw [block012_data_flat024_step]
def block012_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408))]
theorem block012_data_flat025_step : block012_data_flat025 = (CoefficientMerge.fastMerge block012_data_flat023 block012_data_flat024) := by decide +kernel
theorem block012_data_flat025_original : block012_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)) := by
  rw [block012_data_flat025_step, block012_data_flat023_original, block012_data_flat024_original]
def block012_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408))]
theorem block012_data_flat026_step : block012_data_flat026 = (CoefficientMerge.fastMerge block012_data_flat022 block012_data_flat025) := by decide +kernel
theorem block012_data_flat026_original : block012_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded))) := by
  rw [block012_data_flat026_step, block012_data_flat022_original, block012_data_flat025_original]
def block012_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408))]
theorem block012_data_flat027_step : block012_data_flat027 = (CoefficientMerge.fastMerge block012_data_flat021 block012_data_flat026) := by decide +kernel
theorem block012_data_flat027_original : block012_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) := by
  rw [block012_data_flat027_step, block012_data_flat021_original, block012_data_flat026_original]
def block012_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 22810615971840))]
theorem block012_data_flat028_step : block012_data_flat028 = (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) := by decide +kernel
theorem block012_data_flat028_original : block012_data_flat028 = (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) := by
  rw [block012_data_flat028_step]
def block012_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 30722528510208))]
theorem block012_data_flat029_step : block012_data_flat029 = (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded) := by decide +kernel
theorem block012_data_flat029_original : block012_data_flat029 = (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded) := by
  rw [block012_data_flat029_step]
def block012_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208))]
theorem block012_data_flat030_step : block012_data_flat030 = (CoefficientMerge.fastMerge block012_data_flat028 block012_data_flat029) := by decide +kernel
theorem block012_data_flat030_original : block012_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) := by
  rw [block012_data_flat030_step, block012_data_flat028_original, block012_data_flat029_original]
def block012_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 30744200282112))]
theorem block012_data_flat031_step : block012_data_flat031 = (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) := by decide +kernel
theorem block012_data_flat031_original : block012_data_flat031 = (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) := by
  rw [block012_data_flat031_step]
def block012_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1489, Int.ofNat (nat_lit 35800014965760))]
theorem block012_data_flat032_step : block012_data_flat032 = (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) := by decide +kernel
theorem block012_data_flat032_original : block012_data_flat032 = (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) := by
  rw [block012_data_flat032_step]
def block012_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat033_step : block012_data_flat033 = (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded) := by decide +kernel
theorem block012_data_flat033_original : block012_data_flat033 = (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded) := by
  rw [block012_data_flat033_step]
def block012_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat034_step : block012_data_flat034 = (CoefficientMerge.fastMerge block012_data_flat032 block012_data_flat033) := by decide +kernel
theorem block012_data_flat034_original : block012_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)) := by
  rw [block012_data_flat034_step, block012_data_flat032_original, block012_data_flat033_original]
def block012_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat035_step : block012_data_flat035 = (CoefficientMerge.fastMerge block012_data_flat031 block012_data_flat034) := by decide +kernel
theorem block012_data_flat035_original : block012_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded))) := by
  rw [block012_data_flat035_step, block012_data_flat031_original, block012_data_flat034_original]
def block012_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat036_step : block012_data_flat036 = (CoefficientMerge.fastMerge block012_data_flat030 block012_data_flat035) := by decide +kernel
theorem block012_data_flat036_original : block012_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))) := by
  rw [block012_data_flat036_step, block012_data_flat030_original, block012_data_flat035_original]
def block012_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat037_step : block012_data_flat037 = (CoefficientMerge.fastMerge block012_data_flat027 block012_data_flat036) := by decide +kernel
theorem block012_data_flat037_original : block012_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded))))) := by
  rw [block012_data_flat037_step, block012_data_flat027_original, block012_data_flat036_original]
def block012_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704)), (nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408))]
theorem block012_data_flat038_step : block012_data_flat038 = (CoefficientMerge.fastMerge block012_data_flat018 block012_data_flat037) := by decide +kernel
theorem block012_data_flat038_original : block012_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) := by
  rw [block012_data_flat038_step, block012_data_flat018_original, block012_data_flat037_original]
def block012_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 15309696528000))]
theorem block012_data_flat039_step : block012_data_flat039 = (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) := by decide +kernel
theorem block012_data_flat039_original : block012_data_flat039 = (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) := by
  rw [block012_data_flat039_step]
def block012_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1500, Int.ofNat (nat_lit 28111885603200))]
theorem block012_data_flat040_step : block012_data_flat040 = (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded) := by decide +kernel
theorem block012_data_flat040_original : block012_data_flat040 = (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded) := by
  rw [block012_data_flat040_step]
def block012_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200))]
theorem block012_data_flat041_step : block012_data_flat041 = (CoefficientMerge.fastMerge block012_data_flat039 block012_data_flat040) := by decide +kernel
theorem block012_data_flat041_original : block012_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) := by
  rw [block012_data_flat041_step, block012_data_flat039_original, block012_data_flat040_original]
def block012_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1501, Int.ofNat (nat_lit 27691470979200))]
theorem block012_data_flat042_step : block012_data_flat042 = (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) := by decide +kernel
theorem block012_data_flat042_original : block012_data_flat042 = (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) := by
  rw [block012_data_flat042_step]
def block012_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 27218146838400))]
theorem block012_data_flat043_step : block012_data_flat043 = (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) := by decide +kernel
theorem block012_data_flat043_original : block012_data_flat043 = (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) := by
  rw [block012_data_flat043_step]
def block012_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1503, Int.ofNat (nat_lit 24611186633600))]
theorem block012_data_flat044_step : block012_data_flat044 = (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded) := by decide +kernel
theorem block012_data_flat044_original : block012_data_flat044 = (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded) := by
  rw [block012_data_flat044_step]
def block012_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600))]
theorem block012_data_flat045_step : block012_data_flat045 = (CoefficientMerge.fastMerge block012_data_flat043 block012_data_flat044) := by decide +kernel
theorem block012_data_flat045_original : block012_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)) := by
  rw [block012_data_flat045_step, block012_data_flat043_original, block012_data_flat044_original]
def block012_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600))]
theorem block012_data_flat046_step : block012_data_flat046 = (CoefficientMerge.fastMerge block012_data_flat042 block012_data_flat045) := by decide +kernel
theorem block012_data_flat046_original : block012_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded))) := by
  rw [block012_data_flat046_step, block012_data_flat042_original, block012_data_flat045_original]
def block012_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600))]
theorem block012_data_flat047_step : block012_data_flat047 = (CoefficientMerge.fastMerge block012_data_flat041 block012_data_flat046) := by decide +kernel
theorem block012_data_flat047_original : block012_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) := by
  rw [block012_data_flat047_step, block012_data_flat041_original, block012_data_flat046_original]
def block012_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 24174485193600))]
theorem block012_data_flat048_step : block012_data_flat048 = (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) := by decide +kernel
theorem block012_data_flat048_original : block012_data_flat048 = (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) := by
  rw [block012_data_flat048_step]
def block012_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 24615195696000))]
theorem block012_data_flat049_step : block012_data_flat049 = (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded) := by decide +kernel
theorem block012_data_flat049_original : block012_data_flat049 = (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded) := by
  rw [block012_data_flat049_step]
def block012_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000))]
theorem block012_data_flat050_step : block012_data_flat050 = (CoefficientMerge.fastMerge block012_data_flat048 block012_data_flat049) := by decide +kernel
theorem block012_data_flat050_original : block012_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) := by
  rw [block012_data_flat050_step, block012_data_flat048_original, block012_data_flat049_original]
def block012_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 33795536947200))]
theorem block012_data_flat051_step : block012_data_flat051 = (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) := by decide +kernel
theorem block012_data_flat051_original : block012_data_flat051 = (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) := by
  rw [block012_data_flat051_step]
def block012_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 27092078118000))]
theorem block012_data_flat052_step : block012_data_flat052 = (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) := by decide +kernel
theorem block012_data_flat052_original : block012_data_flat052 = (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) := by
  rw [block012_data_flat052_step]
def block012_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 35654614732800))]
theorem block012_data_flat053_step : block012_data_flat053 = (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded) := by decide +kernel
theorem block012_data_flat053_original : block012_data_flat053 = (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded) := by
  rw [block012_data_flat053_step]
def block012_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800))]
theorem block012_data_flat054_step : block012_data_flat054 = (CoefficientMerge.fastMerge block012_data_flat052 block012_data_flat053) := by decide +kernel
theorem block012_data_flat054_original : block012_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded)) := by
  rw [block012_data_flat054_step, block012_data_flat052_original, block012_data_flat053_original]
def block012_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800))]
theorem block012_data_flat055_step : block012_data_flat055 = (CoefficientMerge.fastMerge block012_data_flat051 block012_data_flat054) := by decide +kernel
theorem block012_data_flat055_original : block012_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))) := by
  rw [block012_data_flat055_step, block012_data_flat051_original, block012_data_flat054_original]
def block012_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800))]
theorem block012_data_flat056_step : block012_data_flat056 = (CoefficientMerge.fastMerge block012_data_flat050 block012_data_flat055) := by decide +kernel
theorem block012_data_flat056_original : block012_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded)))) := by
  rw [block012_data_flat056_step, block012_data_flat050_original, block012_data_flat055_original]
def block012_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800))]
theorem block012_data_flat057_step : block012_data_flat057 = (CoefficientMerge.fastMerge block012_data_flat047 block012_data_flat056) := by decide +kernel
theorem block012_data_flat057_original : block012_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) := by
  rw [block012_data_flat057_step, block012_data_flat047_original, block012_data_flat056_original]
def block012_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 35432355243600))]
theorem block012_data_flat058_step : block012_data_flat058 = (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) := by decide +kernel
theorem block012_data_flat058_original : block012_data_flat058 = (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) := by
  rw [block012_data_flat058_step]
def block012_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 40841126298000))]
theorem block012_data_flat059_step : block012_data_flat059 = (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded) := by decide +kernel
theorem block012_data_flat059_original : block012_data_flat059 = (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded) := by
  rw [block012_data_flat059_step]
def block012_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000))]
theorem block012_data_flat060_step : block012_data_flat060 = (CoefficientMerge.fastMerge block012_data_flat058 block012_data_flat059) := by decide +kernel
theorem block012_data_flat060_original : block012_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) := by
  rw [block012_data_flat060_step, block012_data_flat058_original, block012_data_flat059_original]
def block012_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 46249897352400))]
theorem block012_data_flat061_step : block012_data_flat061 = (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) := by decide +kernel
theorem block012_data_flat061_original : block012_data_flat061 = (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) := by
  rw [block012_data_flat061_step]
def block012_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1521, Int.ofNat (nat_lit 17669334009600))]
theorem block012_data_flat062_step : block012_data_flat062 = (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) := by decide +kernel
theorem block012_data_flat062_original : block012_data_flat062 = (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) := by
  rw [block012_data_flat062_step]
def block012_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1522, Int.ofNat (nat_lit 32970815539200))]
theorem block012_data_flat063_step : block012_data_flat063 = (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded) := by decide +kernel
theorem block012_data_flat063_original : block012_data_flat063 = (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded) := by
  rw [block012_data_flat063_step]
def block012_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200))]
theorem block012_data_flat064_step : block012_data_flat064 = (CoefficientMerge.fastMerge block012_data_flat062 block012_data_flat063) := by decide +kernel
theorem block012_data_flat064_original : block012_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)) := by
  rw [block012_data_flat064_step, block012_data_flat062_original, block012_data_flat063_original]
def block012_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200))]
theorem block012_data_flat065_step : block012_data_flat065 = (CoefficientMerge.fastMerge block012_data_flat061 block012_data_flat064) := by decide +kernel
theorem block012_data_flat065_original : block012_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded))) := by
  rw [block012_data_flat065_step, block012_data_flat061_original, block012_data_flat064_original]
def block012_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200))]
theorem block012_data_flat066_step : block012_data_flat066 = (CoefficientMerge.fastMerge block012_data_flat060 block012_data_flat065) := by decide +kernel
theorem block012_data_flat066_original : block012_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) := by
  rw [block012_data_flat066_step, block012_data_flat060_original, block012_data_flat065_original]
def block012_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1523, Int.ofNat (nat_lit 31824828000000))]
theorem block012_data_flat067_step : block012_data_flat067 = (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) := by decide +kernel
theorem block012_data_flat067_original : block012_data_flat067 = (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) := by
  rw [block012_data_flat067_step]
def block012_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1524, Int.ofNat (nat_lit 29231398380800))]
theorem block012_data_flat068_step : block012_data_flat068 = (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded) := by decide +kernel
theorem block012_data_flat068_original : block012_data_flat068 = (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded) := by
  rw [block012_data_flat068_step]
def block012_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800))]
theorem block012_data_flat069_step : block012_data_flat069 = (CoefficientMerge.fastMerge block012_data_flat067 block012_data_flat068) := by decide +kernel
theorem block012_data_flat069_original : block012_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) := by
  rw [block012_data_flat069_step, block012_data_flat067_original, block012_data_flat068_original]
def block012_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 28381047609600))]
theorem block012_data_flat070_step : block012_data_flat070 = (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) := by decide +kernel
theorem block012_data_flat070_original : block012_data_flat070 = (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) := by
  rw [block012_data_flat070_step]
def block012_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 28408108780800))]
theorem block012_data_flat071_step : block012_data_flat071 = (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) := by decide +kernel
theorem block012_data_flat071_original : block012_data_flat071 = (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) := by
  rw [block012_data_flat071_step]
def block012_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat072_step : block012_data_flat072 = (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded) := by decide +kernel
theorem block012_data_flat072_original : block012_data_flat072 = (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded) := by
  rw [block012_data_flat072_step]
def block012_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat073_step : block012_data_flat073 = (CoefficientMerge.fastMerge block012_data_flat071 block012_data_flat072) := by decide +kernel
theorem block012_data_flat073_original : block012_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded)) := by
  rw [block012_data_flat073_step, block012_data_flat071_original, block012_data_flat072_original]
def block012_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat074_step : block012_data_flat074 = (CoefficientMerge.fastMerge block012_data_flat070 block012_data_flat073) := by decide +kernel
theorem block012_data_flat074_original : block012_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))) := by
  rw [block012_data_flat074_step, block012_data_flat070_original, block012_data_flat073_original]
def block012_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat075_step : block012_data_flat075 = (CoefficientMerge.fastMerge block012_data_flat069 block012_data_flat074) := by decide +kernel
theorem block012_data_flat075_original : block012_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded)))) := by
  rw [block012_data_flat075_step, block012_data_flat069_original, block012_data_flat074_original]
def block012_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat076_step : block012_data_flat076 = (CoefficientMerge.fastMerge block012_data_flat066 block012_data_flat075) := by decide +kernel
theorem block012_data_flat076_original : block012_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))) := by
  rw [block012_data_flat076_step, block012_data_flat066_original, block012_data_flat075_original]
def block012_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800)), (nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat077_step : block012_data_flat077 = (CoefficientMerge.fastMerge block012_data_flat057 block012_data_flat076) := by decide +kernel
theorem block012_data_flat077_original : block012_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded)))))) := by
  rw [block012_data_flat077_step, block012_data_flat057_original, block012_data_flat076_original]
def block012_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704)), (nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408)), (nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800)), (nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600))]
theorem block012_data_flat078_step : block012_data_flat078 = (CoefficientMerge.fastMerge block012_data_flat038 block012_data_flat077) := by decide +kernel
theorem block012_data_flat078_original : block012_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))))) := by
  rw [block012_data_flat078_step, block012_data_flat038_original, block012_data_flat077_original]
def block012_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800))]
theorem block012_data_flat079_step : block012_data_flat079 = (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) := by decide +kernel
theorem block012_data_flat079_original : block012_data_flat079 = (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) := by
  rw [block012_data_flat079_step]
def block012_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 40436710272000))]
theorem block012_data_flat080_step : block012_data_flat080 = (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded) := by decide +kernel
theorem block012_data_flat080_original : block012_data_flat080 = (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded) := by
  rw [block012_data_flat080_step]
def block012_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000))]
theorem block012_data_flat081_step : block012_data_flat081 = (CoefficientMerge.fastMerge block012_data_flat079 block012_data_flat080) := by decide +kernel
theorem block012_data_flat081_original : block012_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) := by
  rw [block012_data_flat081_step, block012_data_flat079_original, block012_data_flat080_original]
def block012_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 38977066648800))]
theorem block012_data_flat082_step : block012_data_flat082 = (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) := by decide +kernel
theorem block012_data_flat082_original : block012_data_flat082 = (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) := by
  rw [block012_data_flat082_step]
def block012_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1531, Int.ofNat (nat_lit 44597253103200))]
theorem block012_data_flat083_step : block012_data_flat083 = (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) := by decide +kernel
theorem block012_data_flat083_original : block012_data_flat083 = (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) := by
  rw [block012_data_flat083_step]
def block012_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1532, Int.ofNat (nat_lit 50217439557600))]
theorem block012_data_flat084_step : block012_data_flat084 = (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded) := by decide +kernel
theorem block012_data_flat084_original : block012_data_flat084 = (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded) := by
  rw [block012_data_flat084_step]
def block012_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600))]
theorem block012_data_flat085_step : block012_data_flat085 = (CoefficientMerge.fastMerge block012_data_flat083 block012_data_flat084) := by decide +kernel
theorem block012_data_flat085_original : block012_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)) := by
  rw [block012_data_flat085_step, block012_data_flat083_original, block012_data_flat084_original]
def block012_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600))]
theorem block012_data_flat086_step : block012_data_flat086 = (CoefficientMerge.fastMerge block012_data_flat082 block012_data_flat085) := by decide +kernel
theorem block012_data_flat086_original : block012_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded))) := by
  rw [block012_data_flat086_step, block012_data_flat082_original, block012_data_flat085_original]
def block012_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600))]
theorem block012_data_flat087_step : block012_data_flat087 = (CoefficientMerge.fastMerge block012_data_flat081 block012_data_flat086) := by decide +kernel
theorem block012_data_flat087_original : block012_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) := by
  rw [block012_data_flat087_step, block012_data_flat081_original, block012_data_flat086_original]
def block012_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 20168626464000))]
theorem block012_data_flat088_step : block012_data_flat088 = (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) := by decide +kernel
theorem block012_data_flat088_original : block012_data_flat088 = (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) := by
  rw [block012_data_flat088_step]
def block012_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 37845938592000))]
theorem block012_data_flat089_step : block012_data_flat089 = (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded) := by decide +kernel
theorem block012_data_flat089_original : block012_data_flat089 = (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded) := by
  rw [block012_data_flat089_step]
def block012_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000))]
theorem block012_data_flat090_step : block012_data_flat090 = (CoefficientMerge.fastMerge block012_data_flat088 block012_data_flat089) := by decide +kernel
theorem block012_data_flat090_original : block012_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) := by
  rw [block012_data_flat090_step, block012_data_flat088_original, block012_data_flat089_original]
def block012_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1545, Int.ofNat (nat_lit 34243513875200))]
theorem block012_data_flat091_step : block012_data_flat091 = (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) := by decide +kernel
theorem block012_data_flat091_original : block012_data_flat091 = (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) := by
  rw [block012_data_flat091_step]
def block012_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 32811347923200))]
theorem block012_data_flat092_step : block012_data_flat092 = (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) := by decide +kernel
theorem block012_data_flat092_original : block012_data_flat092 = (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) := by
  rw [block012_data_flat092_step]
def block012_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1547, Int.ofNat (nat_lit 32256593913600))]
theorem block012_data_flat093_step : block012_data_flat093 = (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded) := by decide +kernel
theorem block012_data_flat093_original : block012_data_flat093 = (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded) := by
  rw [block012_data_flat093_step]
def block012_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600))]
theorem block012_data_flat094_step : block012_data_flat094 = (CoefficientMerge.fastMerge block012_data_flat092 block012_data_flat093) := by decide +kernel
theorem block012_data_flat094_original : block012_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded)) := by
  rw [block012_data_flat094_step, block012_data_flat092_original, block012_data_flat093_original]
def block012_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600))]
theorem block012_data_flat095_step : block012_data_flat095 = (CoefficientMerge.fastMerge block012_data_flat091 block012_data_flat094) := by decide +kernel
theorem block012_data_flat095_original : block012_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))) := by
  rw [block012_data_flat095_step, block012_data_flat091_original, block012_data_flat094_original]
def block012_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600))]
theorem block012_data_flat096_step : block012_data_flat096 = (CoefficientMerge.fastMerge block012_data_flat090 block012_data_flat095) := by decide +kernel
theorem block012_data_flat096_original : block012_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded)))) := by
  rw [block012_data_flat096_step, block012_data_flat090_original, block012_data_flat095_original]
def block012_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600))]
theorem block012_data_flat097_step : block012_data_flat097 = (CoefficientMerge.fastMerge block012_data_flat087 block012_data_flat096) := by decide +kernel
theorem block012_data_flat097_original : block012_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) := by
  rw [block012_data_flat097_step, block012_data_flat087_original, block012_data_flat096_original]
def block012_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1548, Int.ofNat (nat_lit 40669074432000))]
theorem block012_data_flat098_step : block012_data_flat098 = (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) := by decide +kernel
theorem block012_data_flat098_original : block012_data_flat098 = (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) := by
  rw [block012_data_flat098_step]
def block012_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1549, Int.ofNat (nat_lit 33480266248800))]
theorem block012_data_flat099_step : block012_data_flat099 = (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded) := by decide +kernel
theorem block012_data_flat099_original : block012_data_flat099 = (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded) := by
  rw [block012_data_flat099_step]
def block012_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800))]
theorem block012_data_flat100_step : block012_data_flat100 = (CoefficientMerge.fastMerge block012_data_flat098 block012_data_flat099) := by decide +kernel
theorem block012_data_flat100_original : block012_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) := by
  rw [block012_data_flat100_step, block012_data_flat098_original, block012_data_flat099_original]
def block012_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1550, Int.ofNat (nat_lit 45218805811200))]
theorem block012_data_flat101_step : block012_data_flat101 = (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) := by decide +kernel
theorem block012_data_flat101_original : block012_data_flat101 = (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) := by
  rw [block012_data_flat101_step]
def block012_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1551, Int.ofNat (nat_lit 41305052224800))]
theorem block012_data_flat102_step : block012_data_flat102 = (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) := by decide +kernel
theorem block012_data_flat102_original : block012_data_flat102 = (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) := by
  rw [block012_data_flat102_step]
def block012_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1552, Int.ofNat (nat_lit 46701984016800))]
theorem block012_data_flat103_step : block012_data_flat103 = (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded) := by decide +kernel
theorem block012_data_flat103_original : block012_data_flat103 = (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded) := by
  rw [block012_data_flat103_step]
def block012_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800))]
theorem block012_data_flat104_step : block012_data_flat104 = (CoefficientMerge.fastMerge block012_data_flat102 block012_data_flat103) := by decide +kernel
theorem block012_data_flat104_original : block012_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)) := by
  rw [block012_data_flat104_step, block012_data_flat102_original, block012_data_flat103_original]
def block012_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800))]
theorem block012_data_flat105_step : block012_data_flat105 = (CoefficientMerge.fastMerge block012_data_flat101 block012_data_flat104) := by decide +kernel
theorem block012_data_flat105_original : block012_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded))) := by
  rw [block012_data_flat105_step, block012_data_flat101_original, block012_data_flat104_original]
def block012_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800))]
theorem block012_data_flat106_step : block012_data_flat106 = (CoefficientMerge.fastMerge block012_data_flat100 block012_data_flat105) := by decide +kernel
theorem block012_data_flat106_original : block012_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) := by
  rw [block012_data_flat106_step, block012_data_flat100_original, block012_data_flat105_original]
def block012_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 52098915808800))]
theorem block012_data_flat107_step : block012_data_flat107 = (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) := by decide +kernel
theorem block012_data_flat107_original : block012_data_flat107 = (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) := by
  rw [block012_data_flat107_step]
def block012_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 22544457062400))]
theorem block012_data_flat108_step : block012_data_flat108 = (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded) := by decide +kernel
theorem block012_data_flat108_original : block012_data_flat108 = (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded) := by
  rw [block012_data_flat108_step]
def block012_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400))]
theorem block012_data_flat109_step : block012_data_flat109 = (CoefficientMerge.fastMerge block012_data_flat107 block012_data_flat108) := by decide +kernel
theorem block012_data_flat109_original : block012_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) := by
  rw [block012_data_flat109_step, block012_data_flat107_original, block012_data_flat108_original]
def block012_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1566, Int.ofNat (nat_lit 39286802777600))]
theorem block012_data_flat110_step : block012_data_flat110 = (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) := by decide +kernel
theorem block012_data_flat110_original : block012_data_flat110 = (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) := by
  rw [block012_data_flat110_step]
def block012_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1567, Int.ofNat (nat_lit 37104655795200))]
theorem block012_data_flat111_step : block012_data_flat111 = (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) := by decide +kernel
theorem block012_data_flat111_original : block012_data_flat111 = (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) := by
  rw [block012_data_flat111_step]
def block012_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat112_step : block012_data_flat112 = (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded) := by decide +kernel
theorem block012_data_flat112_original : block012_data_flat112 = (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded) := by
  rw [block012_data_flat112_step]
def block012_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat113_step : block012_data_flat113 = (CoefficientMerge.fastMerge block012_data_flat111 block012_data_flat112) := by decide +kernel
theorem block012_data_flat113_original : block012_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)) := by
  rw [block012_data_flat113_step, block012_data_flat111_original, block012_data_flat112_original]
def block012_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat114_step : block012_data_flat114 = (CoefficientMerge.fastMerge block012_data_flat110 block012_data_flat113) := by decide +kernel
theorem block012_data_flat114_original : block012_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded))) := by
  rw [block012_data_flat114_step, block012_data_flat110_original, block012_data_flat113_original]
def block012_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat115_step : block012_data_flat115 = (CoefficientMerge.fastMerge block012_data_flat109 block012_data_flat114) := by decide +kernel
theorem block012_data_flat115_original : block012_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))) := by
  rw [block012_data_flat115_step, block012_data_flat109_original, block012_data_flat114_original]
def block012_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat116_step : block012_data_flat116 = (CoefficientMerge.fastMerge block012_data_flat106 block012_data_flat115) := by decide +kernel
theorem block012_data_flat116_original : block012_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded))))) := by
  rw [block012_data_flat116_step, block012_data_flat106_original, block012_data_flat115_original]
def block012_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600)), (nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200))]
theorem block012_data_flat117_step : block012_data_flat117 = (CoefficientMerge.fastMerge block012_data_flat097 block012_data_flat116) := by decide +kernel
theorem block012_data_flat117_original : block012_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) := by
  rw [block012_data_flat117_step, block012_data_flat097_original, block012_data_flat116_original]
def block012_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 43481996006400))]
theorem block012_data_flat118_step : block012_data_flat118 = (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) := by decide +kernel
theorem block012_data_flat118_original : block012_data_flat118 = (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) := by
  rw [block012_data_flat118_step]
def block012_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1570, Int.ofNat (nat_lit 35727947136000))]
theorem block012_data_flat119_step : block012_data_flat119 = (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded) := by decide +kernel
theorem block012_data_flat119_original : block012_data_flat119 = (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded) := by
  rw [block012_data_flat119_step]
def block012_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000))]
theorem block012_data_flat120_step : block012_data_flat120 = (CoefficientMerge.fastMerge block012_data_flat118 block012_data_flat119) := by decide +kernel
theorem block012_data_flat120_original : block012_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) := by
  rw [block012_data_flat120_step, block012_data_flat118_original, block012_data_flat119_original]
def block012_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1571, Int.ofNat (nat_lit 49377054182400))]
theorem block012_data_flat121_step : block012_data_flat121 = (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) := by decide +kernel
theorem block012_data_flat121_original : block012_data_flat121 = (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) := by
  rw [block012_data_flat121_step]
def block012_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1572, Int.ofNat (nat_lit 42461403264000))]
theorem block012_data_flat122_step : block012_data_flat122 = (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) := by decide +kernel
theorem block012_data_flat122_original : block012_data_flat122 = (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) := by
  rw [block012_data_flat122_step]
def block012_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1573, Int.ofNat (nat_lit 47380775500800))]
theorem block012_data_flat123_step : block012_data_flat123 = (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded) := by decide +kernel
theorem block012_data_flat123_original : block012_data_flat123 = (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded) := by
  rw [block012_data_flat123_step]
def block012_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800))]
theorem block012_data_flat124_step : block012_data_flat124 = (CoefficientMerge.fastMerge block012_data_flat122 block012_data_flat123) := by decide +kernel
theorem block012_data_flat124_original : block012_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)) := by
  rw [block012_data_flat124_step, block012_data_flat122_original, block012_data_flat123_original]
def block012_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800))]
theorem block012_data_flat125_step : block012_data_flat125 = (CoefficientMerge.fastMerge block012_data_flat121 block012_data_flat124) := by decide +kernel
theorem block012_data_flat125_original : block012_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded))) := by
  rw [block012_data_flat125_step, block012_data_flat121_original, block012_data_flat124_original]
def block012_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800))]
theorem block012_data_flat126_step : block012_data_flat126 = (CoefficientMerge.fastMerge block012_data_flat120 block012_data_flat125) := by decide +kernel
theorem block012_data_flat126_original : block012_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) := by
  rw [block012_data_flat126_step, block012_data_flat120_original, block012_data_flat125_original]
def block012_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 52300147737600))]
theorem block012_data_flat127_step : block012_data_flat127 = (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) := by decide +kernel
theorem block012_data_flat127_original : block012_data_flat127 = (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) := by
  rw [block012_data_flat127_step]
def block012_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1587, Int.ofNat (nat_lit 22036670566400))]
theorem block012_data_flat128_step : block012_data_flat128 = (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded) := by decide +kernel
theorem block012_data_flat128_original : block012_data_flat128 = (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded) := by
  rw [block012_data_flat128_step]
def block012_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400))]
theorem block012_data_flat129_step : block012_data_flat129 = (CoefficientMerge.fastMerge block012_data_flat127 block012_data_flat128) := by decide +kernel
theorem block012_data_flat129_original : block012_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) := by
  rw [block012_data_flat129_step, block012_data_flat127_original, block012_data_flat128_original]
def block012_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1588, Int.ofNat (nat_lit 40545867353600))]
theorem block012_data_flat130_step : block012_data_flat130 = (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) := by decide +kernel
theorem block012_data_flat130_original : block012_data_flat130 = (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) := by
  rw [block012_data_flat130_step]
def block012_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1589, Int.ofNat (nat_lit 38322985433600))]
theorem block012_data_flat131_step : block012_data_flat131 = (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) := by decide +kernel
theorem block012_data_flat131_original : block012_data_flat131 = (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) := by
  rw [block012_data_flat131_step]
def block012_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1590, Int.ofNat (nat_lit 42195811302400))]
theorem block012_data_flat132_step : block012_data_flat132 = (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded) := by decide +kernel
theorem block012_data_flat132_original : block012_data_flat132 = (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded) := by
  rw [block012_data_flat132_step]
def block012_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400))]
theorem block012_data_flat133_step : block012_data_flat133 = (CoefficientMerge.fastMerge block012_data_flat131 block012_data_flat132) := by decide +kernel
theorem block012_data_flat133_original : block012_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded)) := by
  rw [block012_data_flat133_step, block012_data_flat131_original, block012_data_flat132_original]
def block012_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400))]
theorem block012_data_flat134_step : block012_data_flat134 = (CoefficientMerge.fastMerge block012_data_flat130 block012_data_flat133) := by decide +kernel
theorem block012_data_flat134_original : block012_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))) := by
  rw [block012_data_flat134_step, block012_data_flat130_original, block012_data_flat133_original]
def block012_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400))]
theorem block012_data_flat135_step : block012_data_flat135 = (CoefficientMerge.fastMerge block012_data_flat129 block012_data_flat134) := by decide +kernel
theorem block012_data_flat135_original : block012_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded)))) := by
  rw [block012_data_flat135_step, block012_data_flat129_original, block012_data_flat134_original]
def block012_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400))]
theorem block012_data_flat136_step : block012_data_flat136 = (CoefficientMerge.fastMerge block012_data_flat126 block012_data_flat135) := by decide +kernel
theorem block012_data_flat136_original : block012_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) := by
  rw [block012_data_flat136_step, block012_data_flat126_original, block012_data_flat135_original]
def block012_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1591, Int.ofNat (nat_lit 36822593830400))]
theorem block012_data_flat137_step : block012_data_flat137 = (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) := by decide +kernel
theorem block012_data_flat137_original : block012_data_flat137 = (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) := by
  rw [block012_data_flat137_step]
def block012_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1592, Int.ofNat (nat_lit 49436196275200))]
theorem block012_data_flat138_step : block012_data_flat138 = (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded) := by decide +kernel
theorem block012_data_flat138_original : block012_data_flat138 = (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded) := by
  rw [block012_data_flat138_step]
def block012_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200))]
theorem block012_data_flat139_step : block012_data_flat139 = (CoefficientMerge.fastMerge block012_data_flat137 block012_data_flat138) := by decide +kernel
theorem block012_data_flat139_original : block012_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) := by
  rw [block012_data_flat139_step, block012_data_flat137_original, block012_data_flat138_original]
def block012_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1593, Int.ofNat (nat_lit 43193208755200))]
theorem block012_data_flat140_step : block012_data_flat140 = (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) := by decide +kernel
theorem block012_data_flat140_original : block012_data_flat140 = (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) := by
  rw [block012_data_flat140_step]
def block012_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1594, Int.ofNat (nat_lit 47080567475200))]
theorem block012_data_flat141_step : block012_data_flat141 = (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) := by decide +kernel
theorem block012_data_flat141_original : block012_data_flat141 = (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) := by
  rw [block012_data_flat141_step]
def block012_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1595, Int.ofNat (nat_lit 51625627200000))]
theorem block012_data_flat142_step : block012_data_flat142 = (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded) := by decide +kernel
theorem block012_data_flat142_original : block012_data_flat142 = (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded) := by
  rw [block012_data_flat142_step]
def block012_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000))]
theorem block012_data_flat143_step : block012_data_flat143 = (CoefficientMerge.fastMerge block012_data_flat141 block012_data_flat142) := by decide +kernel
theorem block012_data_flat143_original : block012_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)) := by
  rw [block012_data_flat143_step, block012_data_flat141_original, block012_data_flat142_original]
def block012_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000))]
theorem block012_data_flat144_step : block012_data_flat144 = (CoefficientMerge.fastMerge block012_data_flat140 block012_data_flat143) := by decide +kernel
theorem block012_data_flat144_original : block012_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded))) := by
  rw [block012_data_flat144_step, block012_data_flat140_original, block012_data_flat143_original]
def block012_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000))]
theorem block012_data_flat145_step : block012_data_flat145 = (CoefficientMerge.fastMerge block012_data_flat139 block012_data_flat144) := by decide +kernel
theorem block012_data_flat145_original : block012_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) := by
  rw [block012_data_flat145_step, block012_data_flat139_original, block012_data_flat144_original]
def block012_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1609, Int.ofNat (nat_lit 23512015756800))]
theorem block012_data_flat146_step : block012_data_flat146 = (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) := by decide +kernel
theorem block012_data_flat146_original : block012_data_flat146 = (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) := by
  rw [block012_data_flat146_step]
def block012_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1610, Int.ofNat (nat_lit 42544303142400))]
theorem block012_data_flat147_step : block012_data_flat147 = (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded) := by decide +kernel
theorem block012_data_flat147_original : block012_data_flat147 = (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded) := by
  rw [block012_data_flat147_step]
def block012_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400))]
theorem block012_data_flat148_step : block012_data_flat148 = (CoefficientMerge.fastMerge block012_data_flat146 block012_data_flat147) := by decide +kernel
theorem block012_data_flat148_original : block012_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) := by
  rw [block012_data_flat148_step, block012_data_flat146_original, block012_data_flat147_original]
def block012_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1611, Int.ofNat (nat_lit 45194813697600))]
theorem block012_data_flat149_step : block012_data_flat149 = (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) := by decide +kernel
theorem block012_data_flat149_original : block012_data_flat149 = (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) := by
  rw [block012_data_flat149_step]
def block012_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1612, Int.ofNat (nat_lit 38463278328000))]
theorem block012_data_flat150_step : block012_data_flat150 = (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) := by decide +kernel
theorem block012_data_flat150_original : block012_data_flat150 = (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) := by
  rw [block012_data_flat150_step]
def block012_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat151_step : block012_data_flat151 = (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded) := by decide +kernel
theorem block012_data_flat151_original : block012_data_flat151 = (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded) := by
  rw [block012_data_flat151_step]
def block012_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat152_step : block012_data_flat152 = (CoefficientMerge.fastMerge block012_data_flat150 block012_data_flat151) := by decide +kernel
theorem block012_data_flat152_original : block012_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)) := by
  rw [block012_data_flat152_step, block012_data_flat150_original, block012_data_flat151_original]
def block012_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat153_step : block012_data_flat153 = (CoefficientMerge.fastMerge block012_data_flat149 block012_data_flat152) := by decide +kernel
theorem block012_data_flat153_original : block012_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded))) := by
  rw [block012_data_flat153_step, block012_data_flat149_original, block012_data_flat152_original]
def block012_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat154_step : block012_data_flat154 = (CoefficientMerge.fastMerge block012_data_flat148 block012_data_flat153) := by decide +kernel
theorem block012_data_flat154_original : block012_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)))) := by
  rw [block012_data_flat154_step, block012_data_flat148_original, block012_data_flat153_original]
def block012_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat155_step : block012_data_flat155 = (CoefficientMerge.fastMerge block012_data_flat145 block012_data_flat154) := by decide +kernel
theorem block012_data_flat155_original : block012_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded))))) := by
  rw [block012_data_flat155_step, block012_data_flat145_original, block012_data_flat154_original]
def block012_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400)), (nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat156_step : block012_data_flat156 = (CoefficientMerge.fastMerge block012_data_flat136 block012_data_flat155) := by decide +kernel
theorem block012_data_flat156_original : block012_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)))))) := by
  rw [block012_data_flat156_step, block012_data_flat136_original, block012_data_flat155_original]
def block012_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600)), (nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200)), (nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400)), (nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat157_step : block012_data_flat157 = (CoefficientMerge.fastMerge block012_data_flat117 block012_data_flat156) := by decide +kernel
theorem block012_data_flat157_original : block012_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded))))))) := by
  rw [block012_data_flat157_step, block012_data_flat117_original, block012_data_flat156_original]
def block012_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704)), (nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408)), (nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800)), (nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600)), (nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600)), (nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200)), (nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400)), (nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat158_step : block012_data_flat158 = (CoefficientMerge.fastMerge block012_data_flat078 block012_data_flat157) := by decide +kernel
theorem block012_data_flat158_original : block012_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)))))))) := by
  rw [block012_data_flat158_step, block012_data_flat078_original, block012_data_flat157_original]
def block012_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 24718775961600)), (nat_lit 1465, Int.ofNat (nat_lit 16729808256000)), (nat_lit 1466, Int.ofNat (nat_lit 23887200153600)), (nat_lit 1467, Int.ofNat (nat_lit 25103061043200)), (nat_lit 1468, Int.ofNat (nat_lit 30426215500800)), (nat_lit 1469, Int.ofNat (nat_lit 35749369958400)), (nat_lit 1477, Int.ofNat (nat_lit 13525981519104)), (nat_lit 1478, Int.ofNat (nat_lit 23968533112704)), (nat_lit 1479, Int.ofNat (nat_lit 21615660923904)), (nat_lit 1480, Int.ofNat (nat_lit 21699743848704)), (nat_lit 1481, Int.ofNat (nat_lit 21730917256704)), (nat_lit 1482, Int.ofNat (nat_lit 19796620450304)), (nat_lit 1483, Int.ofNat (nat_lit 19605402491904)), (nat_lit 1484, Int.ofNat (nat_lit 20291596475904)), (nat_lit 1485, Int.ofNat (nat_lit 30208777521408)), (nat_lit 1486, Int.ofNat (nat_lit 22810615971840)), (nat_lit 1487, Int.ofNat (nat_lit 30722528510208)), (nat_lit 1488, Int.ofNat (nat_lit 30744200282112)), (nat_lit 1489, Int.ofNat (nat_lit 35800014965760)), (nat_lit 1490, Int.ofNat (nat_lit 40855829649408)), (nat_lit 1499, Int.ofNat (nat_lit 15309696528000)), (nat_lit 1500, Int.ofNat (nat_lit 28111885603200)), (nat_lit 1501, Int.ofNat (nat_lit 27691470979200)), (nat_lit 1502, Int.ofNat (nat_lit 27218146838400)), (nat_lit 1503, Int.ofNat (nat_lit 24611186633600)), (nat_lit 1504, Int.ofNat (nat_lit 24174485193600)), (nat_lit 1505, Int.ofNat (nat_lit 24615195696000)), (nat_lit 1506, Int.ofNat (nat_lit 33795536947200)), (nat_lit 1507, Int.ofNat (nat_lit 27092078118000)), (nat_lit 1508, Int.ofNat (nat_lit 35654614732800)), (nat_lit 1509, Int.ofNat (nat_lit 35432355243600)), (nat_lit 1510, Int.ofNat (nat_lit 40841126298000)), (nat_lit 1511, Int.ofNat (nat_lit 46249897352400)), (nat_lit 1521, Int.ofNat (nat_lit 17669334009600)), (nat_lit 1522, Int.ofNat (nat_lit 32970815539200)), (nat_lit 1523, Int.ofNat (nat_lit 31824828000000)), (nat_lit 1524, Int.ofNat (nat_lit 29231398380800)), (nat_lit 1525, Int.ofNat (nat_lit 28381047609600)), (nat_lit 1526, Int.ofNat (nat_lit 28408108780800)), (nat_lit 1527, Int.ofNat (nat_lit 37232305689600)), (nat_lit 1528, Int.ofNat (nat_lit 30526491088800)), (nat_lit 1529, Int.ofNat (nat_lit 40436710272000)), (nat_lit 1530, Int.ofNat (nat_lit 38977066648800)), (nat_lit 1531, Int.ofNat (nat_lit 44597253103200)), (nat_lit 1532, Int.ofNat (nat_lit 50217439557600)), (nat_lit 1543, Int.ofNat (nat_lit 20168626464000)), (nat_lit 1544, Int.ofNat (nat_lit 37845938592000)), (nat_lit 1545, Int.ofNat (nat_lit 34243513875200)), (nat_lit 1546, Int.ofNat (nat_lit 32811347923200)), (nat_lit 1547, Int.ofNat (nat_lit 32256593913600)), (nat_lit 1548, Int.ofNat (nat_lit 40669074432000)), (nat_lit 1549, Int.ofNat (nat_lit 33480266248800)), (nat_lit 1550, Int.ofNat (nat_lit 45218805811200)), (nat_lit 1551, Int.ofNat (nat_lit 41305052224800)), (nat_lit 1552, Int.ofNat (nat_lit 46701984016800)), (nat_lit 1553, Int.ofNat (nat_lit 52098915808800)), (nat_lit 1565, Int.ofNat (nat_lit 22544457062400)), (nat_lit 1566, Int.ofNat (nat_lit 39286802777600)), (nat_lit 1567, Int.ofNat (nat_lit 37104655795200)), (nat_lit 1568, Int.ofNat (nat_lit 35799920755200)), (nat_lit 1569, Int.ofNat (nat_lit 43481996006400)), (nat_lit 1570, Int.ofNat (nat_lit 35727947136000)), (nat_lit 1571, Int.ofNat (nat_lit 49377054182400)), (nat_lit 1572, Int.ofNat (nat_lit 42461403264000)), (nat_lit 1573, Int.ofNat (nat_lit 47380775500800)), (nat_lit 1574, Int.ofNat (nat_lit 52300147737600)), (nat_lit 1587, Int.ofNat (nat_lit 22036670566400)), (nat_lit 1588, Int.ofNat (nat_lit 40545867353600)), (nat_lit 1589, Int.ofNat (nat_lit 38322985433600)), (nat_lit 1590, Int.ofNat (nat_lit 42195811302400)), (nat_lit 1591, Int.ofNat (nat_lit 36822593830400)), (nat_lit 1592, Int.ofNat (nat_lit 49436196275200)), (nat_lit 1593, Int.ofNat (nat_lit 43193208755200)), (nat_lit 1594, Int.ofNat (nat_lit 47080567475200)), (nat_lit 1595, Int.ofNat (nat_lit 51625627200000)), (nat_lit 1609, Int.ofNat (nat_lit 23512015756800)), (nat_lit 1610, Int.ofNat (nat_lit 42544303142400)), (nat_lit 1611, Int.ofNat (nat_lit 45194813697600)), (nat_lit 1612, Int.ofNat (nat_lit 38463278328000)), (nat_lit 1613, Int.ofNat (nat_lit 52981496064000))]
theorem block012_data_flat159_step : block012_data_flat159 = (CoefficientMerge.trim block012_data_flat158) := by decide +kernel
theorem block012_data_flat159_original : block012_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded))))))))) := by
  rw [block012_data_flat159_step, block012_data_flat158_original]
theorem block012_data : block012 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)))))))) := by
  have h : block012 = block012_data_flat159 := by decide +kernel
  exact h.trans block012_data_flat159_original
theorem block012_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block012 := by
  rw [block012_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0816Coded_nonneg g hg hA hB) (atom0817Coded_nonneg g hg hA hB)) (add_nonneg (atom0818Coded_nonneg g hg hA hB) (add_nonneg (atom0819Coded_nonneg g hg hA hB) (atom0820Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0821Coded_nonneg g hg hA hB) (atom0822Coded_nonneg g hg hA hB)) (add_nonneg (atom0823Coded_nonneg g hg hA hB) (add_nonneg (atom0824Coded_nonneg g hg hA hB) (atom0825Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0826Coded_nonneg g hg hA hB) (atom0827Coded_nonneg g hg hA hB)) (add_nonneg (atom0828Coded_nonneg g hg hA hB) (add_nonneg (atom0829Coded_nonneg g hg hA hB) (atom0830Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0831Coded_nonneg g hg hA hB) (atom0832Coded_nonneg g hg hA hB)) (add_nonneg (atom0833Coded_nonneg g hg hA hB) (add_nonneg (atom0834Coded_nonneg g hg hA hB) (atom0835Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0836Coded_nonneg g hg hA hB) (atom0837Coded_nonneg g hg hA hB)) (add_nonneg (atom0838Coded_nonneg g hg hA hB) (add_nonneg (atom0839Coded_nonneg g hg hA hB) (atom0840Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0841Coded_nonneg g hg hA hB) (atom0842Coded_nonneg g hg hA hB)) (add_nonneg (atom0843Coded_nonneg g hg hA hB) (add_nonneg (atom0844Coded_nonneg g hg hA hB) (atom0845Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0846Coded_nonneg g hg hA hB) (atom0847Coded_nonneg g hg hA hB)) (add_nonneg (atom0848Coded_nonneg g hg hA hB) (add_nonneg (atom0849Coded_nonneg g hg hA hB) (atom0850Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0851Coded_nonneg g hg hA hB) (atom0852Coded_nonneg g hg hA hB)) (add_nonneg (atom0853Coded_nonneg g hg hA hB) (add_nonneg (atom0854Coded_nonneg g hg hA hB) (atom0855Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0856Coded_nonneg g hg hA hB) (atom0857Coded_nonneg g hg hA hB)) (add_nonneg (atom0858Coded_nonneg g hg hA hB) (add_nonneg (atom0859Coded_nonneg g hg hA hB) (atom0860Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0861Coded_nonneg g hg hA hB) (atom0862Coded_nonneg g hg hA hB)) (add_nonneg (atom0863Coded_nonneg g hg hA hB) (add_nonneg (atom0864Coded_nonneg g hg hA hB) (atom0865Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0866Coded_nonneg g hg hA hB) (atom0867Coded_nonneg g hg hA hB)) (add_nonneg (atom0868Coded_nonneg g hg hA hB) (add_nonneg (atom0869Coded_nonneg g hg hA hB) (atom0870Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0871Coded_nonneg g hg hA hB) (atom0872Coded_nonneg g hg hA hB)) (add_nonneg (atom0873Coded_nonneg g hg hA hB) (add_nonneg (atom0874Coded_nonneg g hg hA hB) (atom0875Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0876Coded_nonneg g hg hA hB) (atom0877Coded_nonneg g hg hA hB)) (add_nonneg (atom0878Coded_nonneg g hg hA hB) (add_nonneg (atom0879Coded_nonneg g hg hA hB) (atom0880Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0881Coded_nonneg g hg hA hB) (atom0882Coded_nonneg g hg hA hB)) (add_nonneg (atom0883Coded_nonneg g hg hA hB) (add_nonneg (atom0884Coded_nonneg g hg hA hB) (atom0885Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0886Coded_nonneg g hg hA hB) (atom0887Coded_nonneg g hg hA hB)) (add_nonneg (atom0888Coded_nonneg g hg hA hB) (add_nonneg (atom0889Coded_nonneg g hg hA hB) (atom0890Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0891Coded_nonneg g hg hA hB) (atom0892Coded_nonneg g hg hA hB)) (add_nonneg (atom0893Coded_nonneg g hg hA hB) (add_nonneg (atom0894Coded_nonneg g hg hA hB) (atom0895Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
