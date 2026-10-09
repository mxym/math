import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0816 : SparsePolynomial.Poly := [([3,6,15], 1)]
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
def atom0816Coded : CoefficientMerge.Poly := [(1464, 1)]
theorem atom0816Coded_decode : atom0816 = SparsePolynomial.decodeCubic 21 atom0816Coded := by decide +kernel
theorem atom0816Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) := by
  have h := atom0816_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0816Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0817 : SparsePolynomial.Poly := [([3,6,16], 1)]
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
def atom0817Coded : CoefficientMerge.Poly := [(1465, 1)]
theorem atom0817Coded_decode : atom0817 = SparsePolynomial.decodeCubic 21 atom0817Coded := by decide +kernel
theorem atom0817Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded) := by
  have h := atom0817_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0817Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0818 : SparsePolynomial.Poly := [([3,6,17], 1)]
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
def atom0818Coded : CoefficientMerge.Poly := [(1466, 1)]
theorem atom0818Coded_decode : atom0818 = SparsePolynomial.decodeCubic 21 atom0818Coded := by decide +kernel
theorem atom0818Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) := by
  have h := atom0818_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0818Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0819 : SparsePolynomial.Poly := [([3,6,18], 1)]
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
def atom0819Coded : CoefficientMerge.Poly := [(1467, 1)]
theorem atom0819Coded_decode : atom0819 = SparsePolynomial.decodeCubic 21 atom0819Coded := by decide +kernel
theorem atom0819Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) := by
  have h := atom0819_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0819Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0820 : SparsePolynomial.Poly := [([3,6,19], 1)]
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
def atom0820Coded : CoefficientMerge.Poly := [(1468, 1)]
theorem atom0820Coded_decode : atom0820 = SparsePolynomial.decodeCubic 21 atom0820Coded := by decide +kernel
theorem atom0820Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded) := by
  have h := atom0820_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0820Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0821 : SparsePolynomial.Poly := [([3,6,20], 1)]
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
def atom0821Coded : CoefficientMerge.Poly := [(1469, 1)]
theorem atom0821Coded_decode : atom0821 = SparsePolynomial.decodeCubic 21 atom0821Coded := by decide +kernel
theorem atom0821Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) := by
  have h := atom0821_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0821Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0822 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0822 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13525981519104 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822Coded : CoefficientMerge.Poly := [(1477, 1)]
theorem atom0822Coded_decode : atom0822 = SparsePolynomial.decodeCubic 21 atom0822Coded := by decide +kernel
theorem atom0822Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded) := by
  have h := atom0822_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0822Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0823 : SparsePolynomial.Poly := [([3,7,8], 1)]
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
def atom0823Coded : CoefficientMerge.Poly := [(1478, 1)]
theorem atom0823Coded_decode : atom0823 = SparsePolynomial.decodeCubic 21 atom0823Coded := by decide +kernel
theorem atom0823Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) := by
  have h := atom0823_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0823Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0824 : SparsePolynomial.Poly := [([3,7,9], 1)]
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
def atom0824Coded : CoefficientMerge.Poly := [(1479, 1)]
theorem atom0824Coded_decode : atom0824 = SparsePolynomial.decodeCubic 21 atom0824Coded := by decide +kernel
theorem atom0824Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) := by
  have h := atom0824_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0824Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0825 : SparsePolynomial.Poly := [([3,7,10], 1)]
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
def atom0825Coded : CoefficientMerge.Poly := [(1480, 1)]
theorem atom0825Coded_decode : atom0825 = SparsePolynomial.decodeCubic 21 atom0825Coded := by decide +kernel
theorem atom0825Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded) := by
  have h := atom0825_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0825Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0826 : SparsePolynomial.Poly := [([3,7,11], 1)]
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
def atom0826Coded : CoefficientMerge.Poly := [(1481, 1)]
theorem atom0826Coded_decode : atom0826 = SparsePolynomial.decodeCubic 21 atom0826Coded := by decide +kernel
theorem atom0826Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) := by
  have h := atom0826_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0826Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0827 : SparsePolynomial.Poly := [([3,7,12], 1)]
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
def atom0827Coded : CoefficientMerge.Poly := [(1482, 1)]
theorem atom0827Coded_decode : atom0827 = SparsePolynomial.decodeCubic 21 atom0827Coded := by decide +kernel
theorem atom0827Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded) := by
  have h := atom0827_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0827Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0828 : SparsePolynomial.Poly := [([3,7,13], 1)]
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
def atom0828Coded : CoefficientMerge.Poly := [(1483, 1)]
theorem atom0828Coded_decode : atom0828 = SparsePolynomial.decodeCubic 21 atom0828Coded := by decide +kernel
theorem atom0828Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) := by
  have h := atom0828_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0828Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0829 : SparsePolynomial.Poly := [([3,7,14], 1)]
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
def atom0829Coded : CoefficientMerge.Poly := [(1484, 1)]
theorem atom0829Coded_decode : atom0829 = SparsePolynomial.decodeCubic 21 atom0829Coded := by decide +kernel
theorem atom0829Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) := by
  have h := atom0829_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0829Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0830 : SparsePolynomial.Poly := [([3,7,15], 1)]
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
def atom0830Coded : CoefficientMerge.Poly := [(1485, 1)]
theorem atom0830Coded_decode : atom0830 = SparsePolynomial.decodeCubic 21 atom0830Coded := by decide +kernel
theorem atom0830Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded) := by
  have h := atom0830_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0830Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0831 : SparsePolynomial.Poly := [([3,7,16], 1)]
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
def atom0831Coded : CoefficientMerge.Poly := [(1486, 1)]
theorem atom0831Coded_decode : atom0831 = SparsePolynomial.decodeCubic 21 atom0831Coded := by decide +kernel
theorem atom0831Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) := by
  have h := atom0831_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0831Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0832 : SparsePolynomial.Poly := [([3,7,17], 1)]
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
def atom0832Coded : CoefficientMerge.Poly := [(1487, 1)]
theorem atom0832Coded_decode : atom0832 = SparsePolynomial.decodeCubic 21 atom0832Coded := by decide +kernel
theorem atom0832Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded) := by
  have h := atom0832_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0832Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0833 : SparsePolynomial.Poly := [([3,7,18], 1)]
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
def atom0833Coded : CoefficientMerge.Poly := [(1488, 1)]
theorem atom0833Coded_decode : atom0833 = SparsePolynomial.decodeCubic 21 atom0833Coded := by decide +kernel
theorem atom0833Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) := by
  have h := atom0833_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0833Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0834 : SparsePolynomial.Poly := [([3,7,19], 1)]
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
def atom0834Coded : CoefficientMerge.Poly := [(1489, 1)]
theorem atom0834Coded_decode : atom0834 = SparsePolynomial.decodeCubic 21 atom0834Coded := by decide +kernel
theorem atom0834Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) := by
  have h := atom0834_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0834Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0835 : SparsePolynomial.Poly := [([3,7,20], 1)]
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
def atom0835Coded : CoefficientMerge.Poly := [(1490, 1)]
theorem atom0835Coded_decode : atom0835 = SparsePolynomial.decodeCubic 21 atom0835Coded := by decide +kernel
theorem atom0835Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded) := by
  have h := atom0835_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0835Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0836 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0836 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15309696528000 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836Coded : CoefficientMerge.Poly := [(1499, 1)]
theorem atom0836Coded_decode : atom0836 = SparsePolynomial.decodeCubic 21 atom0836Coded := by decide +kernel
theorem atom0836Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) := by
  have h := atom0836_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0836Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0837 : SparsePolynomial.Poly := [([3,8,9], 1)]
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
def atom0837Coded : CoefficientMerge.Poly := [(1500, 1)]
theorem atom0837Coded_decode : atom0837 = SparsePolynomial.decodeCubic 21 atom0837Coded := by decide +kernel
theorem atom0837Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded) := by
  have h := atom0837_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0837Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0838 : SparsePolynomial.Poly := [([3,8,10], 1)]
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
def atom0838Coded : CoefficientMerge.Poly := [(1501, 1)]
theorem atom0838Coded_decode : atom0838 = SparsePolynomial.decodeCubic 21 atom0838Coded := by decide +kernel
theorem atom0838Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) := by
  have h := atom0838_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0838Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0839 : SparsePolynomial.Poly := [([3,8,11], 1)]
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
def atom0839Coded : CoefficientMerge.Poly := [(1502, 1)]
theorem atom0839Coded_decode : atom0839 = SparsePolynomial.decodeCubic 21 atom0839Coded := by decide +kernel
theorem atom0839Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) := by
  have h := atom0839_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0839Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0840 : SparsePolynomial.Poly := [([3,8,12], 1)]
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
def atom0840Coded : CoefficientMerge.Poly := [(1503, 1)]
theorem atom0840Coded_decode : atom0840 = SparsePolynomial.decodeCubic 21 atom0840Coded := by decide +kernel
theorem atom0840Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded) := by
  have h := atom0840_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0840Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0841 : SparsePolynomial.Poly := [([3,8,13], 1)]
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
def atom0841Coded : CoefficientMerge.Poly := [(1504, 1)]
theorem atom0841Coded_decode : atom0841 = SparsePolynomial.decodeCubic 21 atom0841Coded := by decide +kernel
theorem atom0841Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) := by
  have h := atom0841_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0841Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0842 : SparsePolynomial.Poly := [([3,8,14], 1)]
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
def atom0842Coded : CoefficientMerge.Poly := [(1505, 1)]
theorem atom0842Coded_decode : atom0842 = SparsePolynomial.decodeCubic 21 atom0842Coded := by decide +kernel
theorem atom0842Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded) := by
  have h := atom0842_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0842Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0843 : SparsePolynomial.Poly := [([3,8,15], 1)]
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
def atom0843Coded : CoefficientMerge.Poly := [(1506, 1)]
theorem atom0843Coded_decode : atom0843 = SparsePolynomial.decodeCubic 21 atom0843Coded := by decide +kernel
theorem atom0843Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) := by
  have h := atom0843_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0843Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0844 : SparsePolynomial.Poly := [([3,8,16], 1)]
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
def atom0844Coded : CoefficientMerge.Poly := [(1507, 1)]
theorem atom0844Coded_decode : atom0844 = SparsePolynomial.decodeCubic 21 atom0844Coded := by decide +kernel
theorem atom0844Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) := by
  have h := atom0844_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0844Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0845 : SparsePolynomial.Poly := [([3,8,17], 1)]
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
def atom0845Coded : CoefficientMerge.Poly := [(1508, 1)]
theorem atom0845Coded_decode : atom0845 = SparsePolynomial.decodeCubic 21 atom0845Coded := by decide +kernel
theorem atom0845Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded) := by
  have h := atom0845_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0845Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0846 : SparsePolynomial.Poly := [([3,8,18], 1)]
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
def atom0846Coded : CoefficientMerge.Poly := [(1509, 1)]
theorem atom0846Coded_decode : atom0846 = SparsePolynomial.decodeCubic 21 atom0846Coded := by decide +kernel
theorem atom0846Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) := by
  have h := atom0846_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0846Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0847 : SparsePolynomial.Poly := [([3,8,19], 1)]
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
def atom0847Coded : CoefficientMerge.Poly := [(1510, 1)]
theorem atom0847Coded_decode : atom0847 = SparsePolynomial.decodeCubic 21 atom0847Coded := by decide +kernel
theorem atom0847Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded) := by
  have h := atom0847_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0847Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0848 : SparsePolynomial.Poly := [([3,8,20], 1)]
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
def atom0848Coded : CoefficientMerge.Poly := [(1511, 1)]
theorem atom0848Coded_decode : atom0848 = SparsePolynomial.decodeCubic 21 atom0848Coded := by decide +kernel
theorem atom0848Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) := by
  have h := atom0848_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0848Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0849 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom0849 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17669334009600 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849Coded : CoefficientMerge.Poly := [(1521, 1)]
theorem atom0849Coded_decode : atom0849 = SparsePolynomial.decodeCubic 21 atom0849Coded := by decide +kernel
theorem atom0849Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) := by
  have h := atom0849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0850 : SparsePolynomial.Poly := [([3,9,10], 1)]
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
def atom0850Coded : CoefficientMerge.Poly := [(1522, 1)]
theorem atom0850Coded_decode : atom0850 = SparsePolynomial.decodeCubic 21 atom0850Coded := by decide +kernel
theorem atom0850Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded) := by
  have h := atom0850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0851 : SparsePolynomial.Poly := [([3,9,11], 1)]
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
def atom0851Coded : CoefficientMerge.Poly := [(1523, 1)]
theorem atom0851Coded_decode : atom0851 = SparsePolynomial.decodeCubic 21 atom0851Coded := by decide +kernel
theorem atom0851Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) := by
  have h := atom0851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0852 : SparsePolynomial.Poly := [([3,9,12], 1)]
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
def atom0852Coded : CoefficientMerge.Poly := [(1524, 1)]
theorem atom0852Coded_decode : atom0852 = SparsePolynomial.decodeCubic 21 atom0852Coded := by decide +kernel
theorem atom0852Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded) := by
  have h := atom0852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0853 : SparsePolynomial.Poly := [([3,9,13], 1)]
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
def atom0853Coded : CoefficientMerge.Poly := [(1525, 1)]
theorem atom0853Coded_decode : atom0853 = SparsePolynomial.decodeCubic 21 atom0853Coded := by decide +kernel
theorem atom0853Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) := by
  have h := atom0853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0854 : SparsePolynomial.Poly := [([3,9,14], 1)]
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
def atom0854Coded : CoefficientMerge.Poly := [(1526, 1)]
theorem atom0854Coded_decode : atom0854 = SparsePolynomial.decodeCubic 21 atom0854Coded := by decide +kernel
theorem atom0854Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) := by
  have h := atom0854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0855 : SparsePolynomial.Poly := [([3,9,15], 1)]
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
def atom0855Coded : CoefficientMerge.Poly := [(1527, 1)]
theorem atom0855Coded_decode : atom0855 = SparsePolynomial.decodeCubic 21 atom0855Coded := by decide +kernel
theorem atom0855Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded) := by
  have h := atom0855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0856 : SparsePolynomial.Poly := [([3,9,16], 1)]
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
def atom0856Coded : CoefficientMerge.Poly := [(1528, 1)]
theorem atom0856Coded_decode : atom0856 = SparsePolynomial.decodeCubic 21 atom0856Coded := by decide +kernel
theorem atom0856Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) := by
  have h := atom0856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0857 : SparsePolynomial.Poly := [([3,9,17], 1)]
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
def atom0857Coded : CoefficientMerge.Poly := [(1529, 1)]
theorem atom0857Coded_decode : atom0857 = SparsePolynomial.decodeCubic 21 atom0857Coded := by decide +kernel
theorem atom0857Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded) := by
  have h := atom0857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0858 : SparsePolynomial.Poly := [([3,9,18], 1)]
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
def atom0858Coded : CoefficientMerge.Poly := [(1530, 1)]
theorem atom0858Coded_decode : atom0858 = SparsePolynomial.decodeCubic 21 atom0858Coded := by decide +kernel
theorem atom0858Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) := by
  have h := atom0858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0859 : SparsePolynomial.Poly := [([3,9,19], 1)]
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
def atom0859Coded : CoefficientMerge.Poly := [(1531, 1)]
theorem atom0859Coded_decode : atom0859 = SparsePolynomial.decodeCubic 21 atom0859Coded := by decide +kernel
theorem atom0859Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) := by
  have h := atom0859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0860 : SparsePolynomial.Poly := [([3,9,20], 1)]
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
def atom0860Coded : CoefficientMerge.Poly := [(1532, 1)]
theorem atom0860Coded_decode : atom0860 = SparsePolynomial.decodeCubic 21 atom0860Coded := by decide +kernel
theorem atom0860Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded) := by
  have h := atom0860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0861 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom0861 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20168626464000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861Coded : CoefficientMerge.Poly := [(1543, 1)]
theorem atom0861Coded_decode : atom0861 = SparsePolynomial.decodeCubic 21 atom0861Coded := by decide +kernel
theorem atom0861Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) := by
  have h := atom0861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0862 : SparsePolynomial.Poly := [([3,10,11], 1)]
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
def atom0862Coded : CoefficientMerge.Poly := [(1544, 1)]
theorem atom0862Coded_decode : atom0862 = SparsePolynomial.decodeCubic 21 atom0862Coded := by decide +kernel
theorem atom0862Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded) := by
  have h := atom0862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0863 : SparsePolynomial.Poly := [([3,10,12], 1)]
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
def atom0863Coded : CoefficientMerge.Poly := [(1545, 1)]
theorem atom0863Coded_decode : atom0863 = SparsePolynomial.decodeCubic 21 atom0863Coded := by decide +kernel
theorem atom0863Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) := by
  have h := atom0863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0864 : SparsePolynomial.Poly := [([3,10,13], 1)]
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
def atom0864Coded : CoefficientMerge.Poly := [(1546, 1)]
theorem atom0864Coded_decode : atom0864 = SparsePolynomial.decodeCubic 21 atom0864Coded := by decide +kernel
theorem atom0864Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) := by
  have h := atom0864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0865 : SparsePolynomial.Poly := [([3,10,14], 1)]
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
def atom0865Coded : CoefficientMerge.Poly := [(1547, 1)]
theorem atom0865Coded_decode : atom0865 = SparsePolynomial.decodeCubic 21 atom0865Coded := by decide +kernel
theorem atom0865Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded) := by
  have h := atom0865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0866 : SparsePolynomial.Poly := [([3,10,15], 1)]
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
def atom0866Coded : CoefficientMerge.Poly := [(1548, 1)]
theorem atom0866Coded_decode : atom0866 = SparsePolynomial.decodeCubic 21 atom0866Coded := by decide +kernel
theorem atom0866Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) := by
  have h := atom0866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0867 : SparsePolynomial.Poly := [([3,10,16], 1)]
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
def atom0867Coded : CoefficientMerge.Poly := [(1549, 1)]
theorem atom0867Coded_decode : atom0867 = SparsePolynomial.decodeCubic 21 atom0867Coded := by decide +kernel
theorem atom0867Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded) := by
  have h := atom0867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0868 : SparsePolynomial.Poly := [([3,10,17], 1)]
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
def atom0868Coded : CoefficientMerge.Poly := [(1550, 1)]
theorem atom0868Coded_decode : atom0868 = SparsePolynomial.decodeCubic 21 atom0868Coded := by decide +kernel
theorem atom0868Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) := by
  have h := atom0868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0869 : SparsePolynomial.Poly := [([3,10,18], 1)]
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
def atom0869Coded : CoefficientMerge.Poly := [(1551, 1)]
theorem atom0869Coded_decode : atom0869 = SparsePolynomial.decodeCubic 21 atom0869Coded := by decide +kernel
theorem atom0869Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) := by
  have h := atom0869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0870 : SparsePolynomial.Poly := [([3,10,19], 1)]
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
def atom0870Coded : CoefficientMerge.Poly := [(1552, 1)]
theorem atom0870Coded_decode : atom0870 = SparsePolynomial.decodeCubic 21 atom0870Coded := by decide +kernel
theorem atom0870Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded) := by
  have h := atom0870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0871 : SparsePolynomial.Poly := [([3,10,20], 1)]
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
def atom0871Coded : CoefficientMerge.Poly := [(1553, 1)]
theorem atom0871Coded_decode : atom0871 = SparsePolynomial.decodeCubic 21 atom0871Coded := by decide +kernel
theorem atom0871Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) := by
  have h := atom0871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0872 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom0872 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22544457062400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872Coded : CoefficientMerge.Poly := [(1565, 1)]
theorem atom0872Coded_decode : atom0872 = SparsePolynomial.decodeCubic 21 atom0872Coded := by decide +kernel
theorem atom0872Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded) := by
  have h := atom0872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0873 : SparsePolynomial.Poly := [([3,11,12], 1)]
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
def atom0873Coded : CoefficientMerge.Poly := [(1566, 1)]
theorem atom0873Coded_decode : atom0873 = SparsePolynomial.decodeCubic 21 atom0873Coded := by decide +kernel
theorem atom0873Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) := by
  have h := atom0873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0874 : SparsePolynomial.Poly := [([3,11,13], 1)]
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
def atom0874Coded : CoefficientMerge.Poly := [(1567, 1)]
theorem atom0874Coded_decode : atom0874 = SparsePolynomial.decodeCubic 21 atom0874Coded := by decide +kernel
theorem atom0874Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) := by
  have h := atom0874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0875 : SparsePolynomial.Poly := [([3,11,14], 1)]
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
def atom0875Coded : CoefficientMerge.Poly := [(1568, 1)]
theorem atom0875Coded_decode : atom0875 = SparsePolynomial.decodeCubic 21 atom0875Coded := by decide +kernel
theorem atom0875Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded) := by
  have h := atom0875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0876 : SparsePolynomial.Poly := [([3,11,15], 1)]
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
def atom0876Coded : CoefficientMerge.Poly := [(1569, 1)]
theorem atom0876Coded_decode : atom0876 = SparsePolynomial.decodeCubic 21 atom0876Coded := by decide +kernel
theorem atom0876Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) := by
  have h := atom0876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0877 : SparsePolynomial.Poly := [([3,11,16], 1)]
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
def atom0877Coded : CoefficientMerge.Poly := [(1570, 1)]
theorem atom0877Coded_decode : atom0877 = SparsePolynomial.decodeCubic 21 atom0877Coded := by decide +kernel
theorem atom0877Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded) := by
  have h := atom0877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0878 : SparsePolynomial.Poly := [([3,11,17], 1)]
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
def atom0878Coded : CoefficientMerge.Poly := [(1571, 1)]
theorem atom0878Coded_decode : atom0878 = SparsePolynomial.decodeCubic 21 atom0878Coded := by decide +kernel
theorem atom0878Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) := by
  have h := atom0878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0879 : SparsePolynomial.Poly := [([3,11,18], 1)]
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
def atom0879Coded : CoefficientMerge.Poly := [(1572, 1)]
theorem atom0879Coded_decode : atom0879 = SparsePolynomial.decodeCubic 21 atom0879Coded := by decide +kernel
theorem atom0879Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) := by
  have h := atom0879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0880 : SparsePolynomial.Poly := [([3,11,19], 1)]
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
def atom0880Coded : CoefficientMerge.Poly := [(1573, 1)]
theorem atom0880Coded_decode : atom0880 = SparsePolynomial.decodeCubic 21 atom0880Coded := by decide +kernel
theorem atom0880Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded) := by
  have h := atom0880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0881 : SparsePolynomial.Poly := [([3,11,20], 1)]
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
def atom0881Coded : CoefficientMerge.Poly := [(1574, 1)]
theorem atom0881Coded_decode : atom0881 = SparsePolynomial.decodeCubic 21 atom0881Coded := by decide +kernel
theorem atom0881Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) := by
  have h := atom0881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0882 : SparsePolynomial.Poly := [([3,12,12], 1)]
theorem eval_atom0882 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22036670566400 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882Coded : CoefficientMerge.Poly := [(1587, 1)]
theorem atom0882Coded_decode : atom0882 = SparsePolynomial.decodeCubic 21 atom0882Coded := by decide +kernel
theorem atom0882Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded) := by
  have h := atom0882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0883 : SparsePolynomial.Poly := [([3,12,13], 1)]
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
def atom0883Coded : CoefficientMerge.Poly := [(1588, 1)]
theorem atom0883Coded_decode : atom0883 = SparsePolynomial.decodeCubic 21 atom0883Coded := by decide +kernel
theorem atom0883Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) := by
  have h := atom0883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0884 : SparsePolynomial.Poly := [([3,12,14], 1)]
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
def atom0884Coded : CoefficientMerge.Poly := [(1589, 1)]
theorem atom0884Coded_decode : atom0884 = SparsePolynomial.decodeCubic 21 atom0884Coded := by decide +kernel
theorem atom0884Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) := by
  have h := atom0884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0885 : SparsePolynomial.Poly := [([3,12,15], 1)]
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
def atom0885Coded : CoefficientMerge.Poly := [(1590, 1)]
theorem atom0885Coded_decode : atom0885 = SparsePolynomial.decodeCubic 21 atom0885Coded := by decide +kernel
theorem atom0885Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded) := by
  have h := atom0885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0886 : SparsePolynomial.Poly := [([3,12,16], 1)]
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
def atom0886Coded : CoefficientMerge.Poly := [(1591, 1)]
theorem atom0886Coded_decode : atom0886 = SparsePolynomial.decodeCubic 21 atom0886Coded := by decide +kernel
theorem atom0886Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) := by
  have h := atom0886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0887 : SparsePolynomial.Poly := [([3,12,17], 1)]
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
def atom0887Coded : CoefficientMerge.Poly := [(1592, 1)]
theorem atom0887Coded_decode : atom0887 = SparsePolynomial.decodeCubic 21 atom0887Coded := by decide +kernel
theorem atom0887Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded) := by
  have h := atom0887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0888 : SparsePolynomial.Poly := [([3,12,18], 1)]
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
def atom0888Coded : CoefficientMerge.Poly := [(1593, 1)]
theorem atom0888Coded_decode : atom0888 = SparsePolynomial.decodeCubic 21 atom0888Coded := by decide +kernel
theorem atom0888Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) := by
  have h := atom0888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0889 : SparsePolynomial.Poly := [([3,12,19], 1)]
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
def atom0889Coded : CoefficientMerge.Poly := [(1594, 1)]
theorem atom0889Coded_decode : atom0889 = SparsePolynomial.decodeCubic 21 atom0889Coded := by decide +kernel
theorem atom0889Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) := by
  have h := atom0889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0890 : SparsePolynomial.Poly := [([3,12,20], 1)]
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
def atom0890Coded : CoefficientMerge.Poly := [(1595, 1)]
theorem atom0890Coded_decode : atom0890 = SparsePolynomial.decodeCubic 21 atom0890Coded := by decide +kernel
theorem atom0890Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded) := by
  have h := atom0890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0891 : SparsePolynomial.Poly := [([3,13,13], 1)]
theorem eval_atom0891 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23512015756800 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891Coded : CoefficientMerge.Poly := [(1609, 1)]
theorem atom0891Coded_decode : atom0891 = SparsePolynomial.decodeCubic 21 atom0891Coded := by decide +kernel
theorem atom0891Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) := by
  have h := atom0891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0892 : SparsePolynomial.Poly := [([3,13,14], 1)]
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
def atom0892Coded : CoefficientMerge.Poly := [(1610, 1)]
theorem atom0892Coded_decode : atom0892 = SparsePolynomial.decodeCubic 21 atom0892Coded := by decide +kernel
theorem atom0892Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded) := by
  have h := atom0892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0893 : SparsePolynomial.Poly := [([3,13,15], 1)]
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
def atom0893Coded : CoefficientMerge.Poly := [(1611, 1)]
theorem atom0893Coded_decode : atom0893 = SparsePolynomial.decodeCubic 21 atom0893Coded := by decide +kernel
theorem atom0893Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) := by
  have h := atom0893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0894 : SparsePolynomial.Poly := [([3,13,16], 1)]
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
def atom0894Coded : CoefficientMerge.Poly := [(1612, 1)]
theorem atom0894Coded_decode : atom0894 = SparsePolynomial.decodeCubic 21 atom0894Coded := by decide +kernel
theorem atom0894Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) := by
  have h := atom0894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0895 : SparsePolynomial.Poly := [([3,13,17], 1)]
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
def atom0895Coded : CoefficientMerge.Poly := [(1613, 1)]
theorem atom0895Coded_decode : atom0895 = SparsePolynomial.decodeCubic 21 atom0895Coded := by decide +kernel
theorem atom0895Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded) := by
  have h := atom0895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block012 : CoefficientMerge.Poly := [(1464, 24718775961600), (1465, 16729808256000), (1466, 23887200153600), (1467, 25103061043200), (1468, 30426215500800), (1469, 35749369958400), (1477, 13525981519104), (1478, 23968533112704), (1479, 21615660923904), (1480, 21699743848704), (1481, 21730917256704), (1482, 19796620450304), (1483, 19605402491904), (1484, 20291596475904), (1485, 30208777521408), (1486, 22810615971840), (1487, 30722528510208), (1488, 30744200282112), (1489, 35800014965760), (1490, 40855829649408), (1499, 15309696528000), (1500, 28111885603200), (1501, 27691470979200), (1502, 27218146838400), (1503, 24611186633600), (1504, 24174485193600), (1505, 24615195696000), (1506, 33795536947200), (1507, 27092078118000), (1508, 35654614732800), (1509, 35432355243600), (1510, 40841126298000), (1511, 46249897352400), (1521, 17669334009600), (1522, 32970815539200), (1523, 31824828000000), (1524, 29231398380800), (1525, 28381047609600), (1526, 28408108780800), (1527, 37232305689600), (1528, 30526491088800), (1529, 40436710272000), (1530, 38977066648800), (1531, 44597253103200), (1532, 50217439557600), (1543, 20168626464000), (1544, 37845938592000), (1545, 34243513875200), (1546, 32811347923200), (1547, 32256593913600), (1548, 40669074432000), (1549, 33480266248800), (1550, 45218805811200), (1551, 41305052224800), (1552, 46701984016800), (1553, 52098915808800), (1565, 22544457062400), (1566, 39286802777600), (1567, 37104655795200), (1568, 35799920755200), (1569, 43481996006400), (1570, 35727947136000), (1571, 49377054182400), (1572, 42461403264000), (1573, 47380775500800), (1574, 52300147737600), (1587, 22036670566400), (1588, 40545867353600), (1589, 38322985433600), (1590, 42195811302400), (1591, 36822593830400), (1592, 49436196275200), (1593, 43193208755200), (1594, 47080567475200), (1595, 51625627200000), (1609, 23512015756800), (1610, 42544303142400), (1611, 45194813697600), (1612, 38463278328000), (1613, 52981496064000)]
theorem block012_data : block012 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24718775961600 : Int) atom0816Coded) (CoefficientMerge.scale (16729808256000 : Int) atom0817Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23887200153600 : Int) atom0818Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25103061043200 : Int) atom0819Coded) (CoefficientMerge.scale (30426215500800 : Int) atom0820Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35749369958400 : Int) atom0821Coded) (CoefficientMerge.scale (13525981519104 : Int) atom0822Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23968533112704 : Int) atom0823Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21615660923904 : Int) atom0824Coded) (CoefficientMerge.scale (21699743848704 : Int) atom0825Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21730917256704 : Int) atom0826Coded) (CoefficientMerge.scale (19796620450304 : Int) atom0827Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19605402491904 : Int) atom0828Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20291596475904 : Int) atom0829Coded) (CoefficientMerge.scale (30208777521408 : Int) atom0830Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22810615971840 : Int) atom0831Coded) (CoefficientMerge.scale (30722528510208 : Int) atom0832Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30744200282112 : Int) atom0833Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35800014965760 : Int) atom0834Coded) (CoefficientMerge.scale (40855829649408 : Int) atom0835Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15309696528000 : Int) atom0836Coded) (CoefficientMerge.scale (28111885603200 : Int) atom0837Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27691470979200 : Int) atom0838Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27218146838400 : Int) atom0839Coded) (CoefficientMerge.scale (24611186633600 : Int) atom0840Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24174485193600 : Int) atom0841Coded) (CoefficientMerge.scale (24615195696000 : Int) atom0842Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33795536947200 : Int) atom0843Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27092078118000 : Int) atom0844Coded) (CoefficientMerge.scale (35654614732800 : Int) atom0845Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35432355243600 : Int) atom0846Coded) (CoefficientMerge.scale (40841126298000 : Int) atom0847Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46249897352400 : Int) atom0848Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17669334009600 : Int) atom0849Coded) (CoefficientMerge.scale (32970815539200 : Int) atom0850Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31824828000000 : Int) atom0851Coded) (CoefficientMerge.scale (29231398380800 : Int) atom0852Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28381047609600 : Int) atom0853Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28408108780800 : Int) atom0854Coded) (CoefficientMerge.scale (37232305689600 : Int) atom0855Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30526491088800 : Int) atom0856Coded) (CoefficientMerge.scale (40436710272000 : Int) atom0857Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38977066648800 : Int) atom0858Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44597253103200 : Int) atom0859Coded) (CoefficientMerge.scale (50217439557600 : Int) atom0860Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20168626464000 : Int) atom0861Coded) (CoefficientMerge.scale (37845938592000 : Int) atom0862Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34243513875200 : Int) atom0863Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32811347923200 : Int) atom0864Coded) (CoefficientMerge.scale (32256593913600 : Int) atom0865Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40669074432000 : Int) atom0866Coded) (CoefficientMerge.scale (33480266248800 : Int) atom0867Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45218805811200 : Int) atom0868Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41305052224800 : Int) atom0869Coded) (CoefficientMerge.scale (46701984016800 : Int) atom0870Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52098915808800 : Int) atom0871Coded) (CoefficientMerge.scale (22544457062400 : Int) atom0872Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39286802777600 : Int) atom0873Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37104655795200 : Int) atom0874Coded) (CoefficientMerge.scale (35799920755200 : Int) atom0875Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43481996006400 : Int) atom0876Coded) (CoefficientMerge.scale (35727947136000 : Int) atom0877Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49377054182400 : Int) atom0878Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42461403264000 : Int) atom0879Coded) (CoefficientMerge.scale (47380775500800 : Int) atom0880Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52300147737600 : Int) atom0881Coded) (CoefficientMerge.scale (22036670566400 : Int) atom0882Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40545867353600 : Int) atom0883Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38322985433600 : Int) atom0884Coded) (CoefficientMerge.scale (42195811302400 : Int) atom0885Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36822593830400 : Int) atom0886Coded) (CoefficientMerge.scale (49436196275200 : Int) atom0887Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43193208755200 : Int) atom0888Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47080567475200 : Int) atom0889Coded) (CoefficientMerge.scale (51625627200000 : Int) atom0890Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23512015756800 : Int) atom0891Coded) (CoefficientMerge.scale (42544303142400 : Int) atom0892Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45194813697600 : Int) atom0893Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38463278328000 : Int) atom0894Coded) (CoefficientMerge.scale (52981496064000 : Int) atom0895Coded)))))))) := by decide +kernel
theorem block012_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block012 := by
  rw [block012_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0816Coded_nonneg g hg hA hB) (atom0817Coded_nonneg g hg hA hB)) (add_nonneg (atom0818Coded_nonneg g hg hA hB) (add_nonneg (atom0819Coded_nonneg g hg hA hB) (atom0820Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0821Coded_nonneg g hg hA hB) (atom0822Coded_nonneg g hg hA hB)) (add_nonneg (atom0823Coded_nonneg g hg hA hB) (add_nonneg (atom0824Coded_nonneg g hg hA hB) (atom0825Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0826Coded_nonneg g hg hA hB) (atom0827Coded_nonneg g hg hA hB)) (add_nonneg (atom0828Coded_nonneg g hg hA hB) (add_nonneg (atom0829Coded_nonneg g hg hA hB) (atom0830Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0831Coded_nonneg g hg hA hB) (atom0832Coded_nonneg g hg hA hB)) (add_nonneg (atom0833Coded_nonneg g hg hA hB) (add_nonneg (atom0834Coded_nonneg g hg hA hB) (atom0835Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0836Coded_nonneg g hg hA hB) (atom0837Coded_nonneg g hg hA hB)) (add_nonneg (atom0838Coded_nonneg g hg hA hB) (add_nonneg (atom0839Coded_nonneg g hg hA hB) (atom0840Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0841Coded_nonneg g hg hA hB) (atom0842Coded_nonneg g hg hA hB)) (add_nonneg (atom0843Coded_nonneg g hg hA hB) (add_nonneg (atom0844Coded_nonneg g hg hA hB) (atom0845Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0846Coded_nonneg g hg hA hB) (atom0847Coded_nonneg g hg hA hB)) (add_nonneg (atom0848Coded_nonneg g hg hA hB) (add_nonneg (atom0849Coded_nonneg g hg hA hB) (atom0850Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0851Coded_nonneg g hg hA hB) (atom0852Coded_nonneg g hg hA hB)) (add_nonneg (atom0853Coded_nonneg g hg hA hB) (add_nonneg (atom0854Coded_nonneg g hg hA hB) (atom0855Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0856Coded_nonneg g hg hA hB) (atom0857Coded_nonneg g hg hA hB)) (add_nonneg (atom0858Coded_nonneg g hg hA hB) (add_nonneg (atom0859Coded_nonneg g hg hA hB) (atom0860Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0861Coded_nonneg g hg hA hB) (atom0862Coded_nonneg g hg hA hB)) (add_nonneg (atom0863Coded_nonneg g hg hA hB) (add_nonneg (atom0864Coded_nonneg g hg hA hB) (atom0865Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0866Coded_nonneg g hg hA hB) (atom0867Coded_nonneg g hg hA hB)) (add_nonneg (atom0868Coded_nonneg g hg hA hB) (add_nonneg (atom0869Coded_nonneg g hg hA hB) (atom0870Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0871Coded_nonneg g hg hA hB) (atom0872Coded_nonneg g hg hA hB)) (add_nonneg (atom0873Coded_nonneg g hg hA hB) (add_nonneg (atom0874Coded_nonneg g hg hA hB) (atom0875Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0876Coded_nonneg g hg hA hB) (atom0877Coded_nonneg g hg hA hB)) (add_nonneg (atom0878Coded_nonneg g hg hA hB) (add_nonneg (atom0879Coded_nonneg g hg hA hB) (atom0880Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0881Coded_nonneg g hg hA hB) (atom0882Coded_nonneg g hg hA hB)) (add_nonneg (atom0883Coded_nonneg g hg hA hB) (add_nonneg (atom0884Coded_nonneg g hg hA hB) (atom0885Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0886Coded_nonneg g hg hA hB) (atom0887Coded_nonneg g hg hA hB)) (add_nonneg (atom0888Coded_nonneg g hg hA hB) (add_nonneg (atom0889Coded_nonneg g hg hA hB) (atom0890Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0891Coded_nonneg g hg hA hB) (atom0892Coded_nonneg g hg hA hB)) (add_nonneg (atom0893Coded_nonneg g hg hA hB) (add_nonneg (atom0894Coded_nonneg g hg hA hB) (atom0895Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
