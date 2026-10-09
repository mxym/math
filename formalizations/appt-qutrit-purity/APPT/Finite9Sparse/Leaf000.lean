import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0000 : SparsePolynomial.Poly := [([0,0,3], 1)]
theorem eval_atom0000 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0000 = ((g 0) * (g 0) * (g 3)) := by
  norm_num [atom0000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0000_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120240 : Int) atom0000) := by
  rw [SparsePolynomial.eval_scale, eval_atom0000]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 0) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0000Coded : CoefficientMerge.Poly := [(3, 1)]
theorem atom0000Coded_decode : atom0000 = SparsePolynomial.decodeCubic 9 atom0000Coded := by decide +kernel
theorem atom0000Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (120240 : Int) atom0000Coded) := by
  have h := atom0000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0001 : SparsePolynomial.Poly := [([0,0,4], 1)]
theorem eval_atom0001 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0001 = ((g 0) * (g 0) * (g 4)) := by
  norm_num [atom0001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0001_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95040 : Int) atom0001) := by
  rw [SparsePolynomial.eval_scale, eval_atom0001]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 0) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0001Coded : CoefficientMerge.Poly := [(4, 1)]
theorem atom0001Coded_decode : atom0001 = SparsePolynomial.decodeCubic 9 atom0001Coded := by decide +kernel
theorem atom0001Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (95040 : Int) atom0001Coded) := by
  have h := atom0001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0002 : SparsePolynomial.Poly := [([0,0,5], 1)]
theorem eval_atom0002 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0002 = ((g 0) * (g 0) * (g 5)) := by
  norm_num [atom0002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0002_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69840 : Int) atom0002) := by
  rw [SparsePolynomial.eval_scale, eval_atom0002]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 0) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0002Coded : CoefficientMerge.Poly := [(5, 1)]
theorem atom0002Coded_decode : atom0002 = SparsePolynomial.decodeCubic 9 atom0002Coded := by decide +kernel
theorem atom0002Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (69840 : Int) atom0002Coded) := by
  have h := atom0002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0003 : SparsePolynomial.Poly := [([0,0,6], 1)]
theorem eval_atom0003 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0003 = ((g 0) * (g 0) * (g 6)) := by
  norm_num [atom0003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0003_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44640 : Int) atom0003) := by
  rw [SparsePolynomial.eval_scale, eval_atom0003]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 0) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0003Coded : CoefficientMerge.Poly := [(6, 1)]
theorem atom0003Coded_decode : atom0003 = SparsePolynomial.decodeCubic 9 atom0003Coded := by decide +kernel
theorem atom0003Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (44640 : Int) atom0003Coded) := by
  have h := atom0003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0004 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0004 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0004 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0004_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27240 : Int) atom0004) := by
  rw [SparsePolynomial.eval_scale, eval_atom0004]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0004Coded : CoefficientMerge.Poly := [(10, 1)]
theorem atom0004Coded_decode : atom0004 = SparsePolynomial.decodeCubic 9 atom0004Coded := by decide +kernel
theorem atom0004Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (27240 : Int) atom0004Coded) := by
  have h := atom0004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0005 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0005 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0005 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0005_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175680 : Int) atom0005) := by
  rw [SparsePolynomial.eval_scale, eval_atom0005]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0005Coded : CoefficientMerge.Poly := [(11, 1)]
theorem atom0005Coded_decode : atom0005 = SparsePolynomial.decodeCubic 9 atom0005Coded := by decide +kernel
theorem atom0005Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (175680 : Int) atom0005Coded) := by
  have h := atom0005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0006 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0006 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0006 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0006_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (481140 : Int) atom0006) := by
  rw [SparsePolynomial.eval_scale, eval_atom0006]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0006Coded : CoefficientMerge.Poly := [(12, 1)]
theorem atom0006Coded_decode : atom0006 = SparsePolynomial.decodeCubic 9 atom0006Coded := by decide +kernel
theorem atom0006Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (481140 : Int) atom0006Coded) := by
  have h := atom0006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0007 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0007 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0007 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0007_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229160 : Int) atom0007) := by
  rw [SparsePolynomial.eval_scale, eval_atom0007]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0007Coded : CoefficientMerge.Poly := [(13, 1)]
theorem atom0007Coded_decode : atom0007 = SparsePolynomial.decodeCubic 9 atom0007Coded := by decide +kernel
theorem atom0007Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (229160 : Int) atom0007Coded) := by
  have h := atom0007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0008 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0008 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0008 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0008_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126540 : Int) atom0008) := by
  rw [SparsePolynomial.eval_scale, eval_atom0008]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0008Coded : CoefficientMerge.Poly := [(14, 1)]
theorem atom0008Coded_decode : atom0008 = SparsePolynomial.decodeCubic 9 atom0008Coded := by decide +kernel
theorem atom0008Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (126540 : Int) atom0008Coded) := by
  have h := atom0008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0009 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0009 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0009 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0009_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81540 : Int) atom0009) := by
  rw [SparsePolynomial.eval_scale, eval_atom0009]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0009Coded : CoefficientMerge.Poly := [(15, 1)]
theorem atom0009Coded_decode : atom0009 = SparsePolynomial.decodeCubic 9 atom0009Coded := by decide +kernel
theorem atom0009Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (81540 : Int) atom0009Coded) := by
  have h := atom0009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0010 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0010 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0010 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0010_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45520 : Int) atom0010) := by
  rw [SparsePolynomial.eval_scale, eval_atom0010]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0010Coded : CoefficientMerge.Poly := [(16, 1)]
theorem atom0010Coded_decode : atom0010 = SparsePolynomial.decodeCubic 9 atom0010Coded := by decide +kernel
theorem atom0010Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (45520 : Int) atom0010Coded) := by
  have h := atom0010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0011 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0011 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0011 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0011_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219600 : Int) atom0011) := by
  rw [SparsePolynomial.eval_scale, eval_atom0011]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0011Coded : CoefficientMerge.Poly := [(20, 1)]
theorem atom0011Coded_decode : atom0011 = SparsePolynomial.decodeCubic 9 atom0011Coded := by decide +kernel
theorem atom0011Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (219600 : Int) atom0011Coded) := by
  have h := atom0011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0012 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0012 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0012 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0012_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (731160 : Int) atom0012) := by
  rw [SparsePolynomial.eval_scale, eval_atom0012]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0012Coded : CoefficientMerge.Poly := [(21, 1)]
theorem atom0012Coded_decode : atom0012 = SparsePolynomial.decodeCubic 9 atom0012Coded := by decide +kernel
theorem atom0012Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (731160 : Int) atom0012Coded) := by
  have h := atom0012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0013 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0013 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0013 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0013_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (477000 : Int) atom0013) := by
  rw [SparsePolynomial.eval_scale, eval_atom0013]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0013Coded : CoefficientMerge.Poly := [(22, 1)]
theorem atom0013Coded_decode : atom0013 = SparsePolynomial.decodeCubic 9 atom0013Coded := by decide +kernel
theorem atom0013Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (477000 : Int) atom0013Coded) := by
  have h := atom0013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0014 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0014 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0014 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0014_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (313380 : Int) atom0014) := by
  rw [SparsePolynomial.eval_scale, eval_atom0014]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0014Coded : CoefficientMerge.Poly := [(23, 1)]
theorem atom0014Coded_decode : atom0014 = SparsePolynomial.decodeCubic 9 atom0014Coded := by decide +kernel
theorem atom0014Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (313380 : Int) atom0014Coded) := by
  have h := atom0014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0015 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0015 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0015 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0015_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158040 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0015Coded : CoefficientMerge.Poly := [(24, 1)]
theorem atom0015Coded_decode : atom0015 = SparsePolynomial.decodeCubic 9 atom0015Coded := by decide +kernel
theorem atom0015Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (158040 : Int) atom0015Coded) := by
  have h := atom0015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0016 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0016 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0016 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0016_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139500 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016Coded : CoefficientMerge.Poly := [(25, 1)]
theorem atom0016Coded_decode : atom0016 = SparsePolynomial.decodeCubic 9 atom0016Coded := by decide +kernel
theorem atom0016Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (139500 : Int) atom0016Coded) := by
  have h := atom0016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0017 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0017 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0017 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0017_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34200 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017Coded : CoefficientMerge.Poly := [(26, 1)]
theorem atom0017Coded_decode : atom0017 = SparsePolynomial.decodeCubic 9 atom0017Coded := by decide +kernel
theorem atom0017Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (34200 : Int) atom0017Coded) := by
  have h := atom0017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0018 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0018 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (508320 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018Coded : CoefficientMerge.Poly := [(30, 1)]
theorem atom0018Coded_decode : atom0018 = SparsePolynomial.decodeCubic 9 atom0018Coded := by decide +kernel
theorem atom0018Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (508320 : Int) atom0018Coded) := by
  have h := atom0018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0019 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0019 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0019 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0019_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (843120 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019Coded : CoefficientMerge.Poly := [(31, 1)]
theorem atom0019Coded_decode : atom0019 = SparsePolynomial.decodeCubic 9 atom0019Coded := by decide +kernel
theorem atom0019Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (843120 : Int) atom0019Coded) := by
  have h := atom0019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0020 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0020 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0020 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0020_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (804060 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020Coded : CoefficientMerge.Poly := [(32, 1)]
theorem atom0020Coded_decode : atom0020 = SparsePolynomial.decodeCubic 9 atom0020Coded := by decide +kernel
theorem atom0020Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (804060 : Int) atom0020Coded) := by
  have h := atom0020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0021 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0021 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0021 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0021_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (729360 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021Coded : CoefficientMerge.Poly := [(33, 1)]
theorem atom0021Coded_decode : atom0021 = SparsePolynomial.decodeCubic 9 atom0021Coded := by decide +kernel
theorem atom0021Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (729360 : Int) atom0021Coded) := by
  have h := atom0021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0022 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0022 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0022 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0022_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344700 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022Coded : CoefficientMerge.Poly := [(34, 1)]
theorem atom0022Coded_decode : atom0022 = SparsePolynomial.decodeCubic 9 atom0022Coded := by decide +kernel
theorem atom0022Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (344700 : Int) atom0022Coded) := by
  have h := atom0022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0023 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0023 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0023 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0023_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (388080 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023Coded : CoefficientMerge.Poly := [(35, 1)]
theorem atom0023Coded_decode : atom0023 = SparsePolynomial.decodeCubic 9 atom0023Coded := by decide +kernel
theorem atom0023Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (388080 : Int) atom0023Coded) := by
  have h := atom0023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0024 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0024 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382464 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024Coded : CoefficientMerge.Poly := [(40, 1)]
theorem atom0024Coded_decode : atom0024 = SparsePolynomial.decodeCubic 9 atom0024Coded := by decide +kernel
theorem atom0024Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (382464 : Int) atom0024Coded) := by
  have h := atom0024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0025 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0025 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0025 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0025_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (715680 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025Coded : CoefficientMerge.Poly := [(41, 1)]
theorem atom0025Coded_decode : atom0025 = SparsePolynomial.decodeCubic 9 atom0025Coded := by decide +kernel
theorem atom0025Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (715680 : Int) atom0025Coded) := by
  have h := atom0025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0026 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0026 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0026 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0026_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (812160 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026Coded : CoefficientMerge.Poly := [(42, 1)]
theorem atom0026Coded_decode : atom0026 = SparsePolynomial.decodeCubic 9 atom0026Coded := by decide +kernel
theorem atom0026Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (812160 : Int) atom0026Coded) := by
  have h := atom0026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0027 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0027 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0027 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0027_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436500 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027Coded : CoefficientMerge.Poly := [(43, 1)]
theorem atom0027Coded_decode : atom0027 = SparsePolynomial.decodeCubic 9 atom0027Coded := by decide +kernel
theorem atom0027Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (436500 : Int) atom0027Coded) := by
  have h := atom0027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0028 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0028 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0028 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0028_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (544320 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028Coded : CoefficientMerge.Poly := [(44, 1)]
theorem atom0028Coded_decode : atom0028 = SparsePolynomial.decodeCubic 9 atom0028Coded := by decide +kernel
theorem atom0028Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (544320 : Int) atom0028Coded) := by
  have h := atom0028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0029 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0029 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380880 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029Coded : CoefficientMerge.Poly := [(50, 1)]
theorem atom0029Coded_decode : atom0029 = SparsePolynomial.decodeCubic 9 atom0029Coded := by decide +kernel
theorem atom0029Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (380880 : Int) atom0029Coded) := by
  have h := atom0029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0030 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0030 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0030 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0030_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (894960 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030Coded : CoefficientMerge.Poly := [(51, 1)]
theorem atom0030Coded_decode : atom0030 = SparsePolynomial.decodeCubic 9 atom0030Coded := by decide +kernel
theorem atom0030Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (894960 : Int) atom0030Coded) := by
  have h := atom0030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0031 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0031 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0031 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0031_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (500580 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031Coded : CoefficientMerge.Poly := [(52, 1)]
theorem atom0031Coded_decode : atom0031 = SparsePolynomial.decodeCubic 9 atom0031Coded := by decide +kernel
theorem atom0031Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (500580 : Int) atom0031Coded) := by
  have h := atom0031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0032 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0032 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0032 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0032_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470160 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032Coded : CoefficientMerge.Poly := [(53, 1)]
theorem atom0032Coded_decode : atom0032 = SparsePolynomial.decodeCubic 9 atom0032Coded := by decide +kernel
theorem atom0032Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (470160 : Int) atom0032Coded) := by
  have h := atom0032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0033 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0033 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488880 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033Coded : CoefficientMerge.Poly := [(60, 1)]
theorem atom0033Coded_decode : atom0033 = SparsePolynomial.decodeCubic 9 atom0033Coded := by decide +kernel
theorem atom0033Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (488880 : Int) atom0033Coded) := by
  have h := atom0033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0034 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0034 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0034 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0034_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592380 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034Coded : CoefficientMerge.Poly := [(61, 1)]
theorem atom0034Coded_decode : atom0034 = SparsePolynomial.decodeCubic 9 atom0034Coded := by decide +kernel
theorem atom0034Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (592380 : Int) atom0034Coded) := by
  have h := atom0034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0035 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0035 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0035 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0035_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (626400 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035Coded : CoefficientMerge.Poly := [(62, 1)]
theorem atom0035Coded_decode : atom0035 = SparsePolynomial.decodeCubic 9 atom0035Coded := by decide +kernel
theorem atom0035Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (626400 : Int) atom0035Coded) := by
  have h := atom0035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0036 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0036 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60300 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036Coded : CoefficientMerge.Poly := [(70, 1)]
theorem atom0036Coded_decode : atom0036 = SparsePolynomial.decodeCubic 9 atom0036Coded := by decide +kernel
theorem atom0036Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (60300 : Int) atom0036Coded) := by
  have h := atom0036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0037 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0037 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0037 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0037_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110700 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037Coded : CoefficientMerge.Poly := [(71, 1)]
theorem atom0037Coded_decode : atom0037 = SparsePolynomial.decodeCubic 9 atom0037Coded := by decide +kernel
theorem atom0037Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (110700 : Int) atom0037Coded) := by
  have h := atom0037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0038 : SparsePolynomial.Poly := [([1,1,1], 1)]
theorem eval_atom0038 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = ((g 1) * (g 1) * (g 1)) := by
  norm_num [atom0038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 1) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038Coded : CoefficientMerge.Poly := [(91, 1)]
theorem atom0038Coded_decode : atom0038 = SparsePolynomial.decodeCubic 9 atom0038Coded := by decide +kernel
theorem atom0038Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (360 : Int) atom0038Coded) := by
  have h := atom0038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0039 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0039 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0039 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0039_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11280 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039Coded : CoefficientMerge.Poly := [(92, 1)]
theorem atom0039Coded_decode : atom0039 = SparsePolynomial.decodeCubic 9 atom0039Coded := by decide +kernel
theorem atom0039Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (11280 : Int) atom0039Coded) := by
  have h := atom0039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0040 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0040 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0040 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0040_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (209940 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040Coded : CoefficientMerge.Poly := [(93, 1)]
theorem atom0040Coded_decode : atom0040 = SparsePolynomial.decodeCubic 9 atom0040Coded := by decide +kernel
theorem atom0040Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (209940 : Int) atom0040Coded) := by
  have h := atom0040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0041 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0041 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0041 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0041_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1380 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041Coded : CoefficientMerge.Poly := [(96, 1)]
theorem atom0041Coded_decode : atom0041 = SparsePolynomial.decodeCubic 9 atom0041Coded := by decide +kernel
theorem atom0041Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1380 : Int) atom0041Coded) := by
  have h := atom0041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0042 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0042 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0042 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0042_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12960 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042Coded : CoefficientMerge.Poly := [(101, 1)]
theorem atom0042Coded_decode : atom0042 = SparsePolynomial.decodeCubic 9 atom0042Coded := by decide +kernel
theorem atom0042Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (12960 : Int) atom0042Coded) := by
  have h := atom0042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0043 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0043 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0043 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0043_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (538560 : Int) atom0043) := by
  rw [SparsePolynomial.eval_scale, eval_atom0043]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0043Coded : CoefficientMerge.Poly := [(102, 1)]
theorem atom0043Coded_decode : atom0043 = SparsePolynomial.decodeCubic 9 atom0043Coded := by decide +kernel
theorem atom0043Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (538560 : Int) atom0043Coded) := by
  have h := atom0043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0044 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0044 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0044 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0044_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223280 : Int) atom0044) := by
  rw [SparsePolynomial.eval_scale, eval_atom0044]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0044Coded : CoefficientMerge.Poly := [(103, 1)]
theorem atom0044Coded_decode : atom0044 = SparsePolynomial.decodeCubic 9 atom0044Coded := by decide +kernel
theorem atom0044Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (223280 : Int) atom0044Coded) := by
  have h := atom0044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0045 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0045 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0045 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0045_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (334260 : Int) atom0045) := by
  rw [SparsePolynomial.eval_scale, eval_atom0045]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0045Coded : CoefficientMerge.Poly := [(104, 1)]
theorem atom0045Coded_decode : atom0045 = SparsePolynomial.decodeCubic 9 atom0045Coded := by decide +kernel
theorem atom0045Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (334260 : Int) atom0045Coded) := by
  have h := atom0045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0046 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0046 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0046 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0046_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443520 : Int) atom0046) := by
  rw [SparsePolynomial.eval_scale, eval_atom0046]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0046Coded : CoefficientMerge.Poly := [(105, 1)]
theorem atom0046Coded_decode : atom0046 = SparsePolynomial.decodeCubic 9 atom0046Coded := by decide +kernel
theorem atom0046Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (443520 : Int) atom0046Coded) := by
  have h := atom0046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0047 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0047 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0047 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0047_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404920 : Int) atom0047) := by
  rw [SparsePolynomial.eval_scale, eval_atom0047]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0047Coded : CoefficientMerge.Poly := [(106, 1)]
theorem atom0047Coded_decode : atom0047 = SparsePolynomial.decodeCubic 9 atom0047Coded := by decide +kernel
theorem atom0047Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (404920 : Int) atom0047Coded) := by
  have h := atom0047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0048 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0048 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0048 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0048_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (560400 : Int) atom0048) := by
  rw [SparsePolynomial.eval_scale, eval_atom0048]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0048Coded : CoefficientMerge.Poly := [(107, 1)]
theorem atom0048Coded_decode : atom0048 = SparsePolynomial.decodeCubic 9 atom0048Coded := by decide +kernel
theorem atom0048Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (560400 : Int) atom0048Coded) := by
  have h := atom0048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0049 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0049 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0049 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0049_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475200 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049Coded : CoefficientMerge.Poly := [(111, 1)]
theorem atom0049Coded_decode : atom0049 = SparsePolynomial.decodeCubic 9 atom0049Coded := by decide +kernel
theorem atom0049Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (475200 : Int) atom0049Coded) := by
  have h := atom0049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0050 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0050 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0050 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0050_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (655960 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050Coded : CoefficientMerge.Poly := [(112, 1)]
theorem atom0050Coded_decode : atom0050 = SparsePolynomial.decodeCubic 9 atom0050Coded := by decide +kernel
theorem atom0050Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (655960 : Int) atom0050Coded) := by
  have h := atom0050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0051 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0051 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0051 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0051_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (892980 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051Coded : CoefficientMerge.Poly := [(113, 1)]
theorem atom0051Coded_decode : atom0051 = SparsePolynomial.decodeCubic 9 atom0051Coded := by decide +kernel
theorem atom0051Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (892980 : Int) atom0051Coded) := by
  have h := atom0051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0052 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0052 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0052 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0052_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1075680 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052Coded : CoefficientMerge.Poly := [(114, 1)]
theorem atom0052Coded_decode : atom0052 = SparsePolynomial.decodeCubic 9 atom0052Coded := by decide +kernel
theorem atom0052Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1075680 : Int) atom0052Coded) := by
  have h := atom0052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0053 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0053 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0053 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0053_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (559400 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053Coded : CoefficientMerge.Poly := [(115, 1)]
theorem atom0053Coded_decode : atom0053 = SparsePolynomial.decodeCubic 9 atom0053Coded := by decide +kernel
theorem atom0053Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (559400 : Int) atom0053Coded) := by
  have h := atom0053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0054 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0054 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0054 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0054_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (745140 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054Coded : CoefficientMerge.Poly := [(116, 1)]
theorem atom0054Coded_decode : atom0054 = SparsePolynomial.decodeCubic 9 atom0054Coded := by decide +kernel
theorem atom0054Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (745140 : Int) atom0054Coded) := by
  have h := atom0054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0055 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0055 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0055 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0055_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213356 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055Coded : CoefficientMerge.Poly := [(121, 1)]
theorem atom0055Coded_decode : atom0055 = SparsePolynomial.decodeCubic 9 atom0055Coded := by decide +kernel
theorem atom0055Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (213356 : Int) atom0055Coded) := by
  have h := atom0055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0056 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0056 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0056 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0056_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (591100 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056Coded : CoefficientMerge.Poly := [(122, 1)]
theorem atom0056Coded_decode : atom0056 = SparsePolynomial.decodeCubic 9 atom0056Coded := by decide +kernel
theorem atom0056Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (591100 : Int) atom0056Coded) := by
  have h := atom0056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0057 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0057 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0057 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0057_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (968550 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057Coded : CoefficientMerge.Poly := [(123, 1)]
theorem atom0057Coded_decode : atom0057 = SparsePolynomial.decodeCubic 9 atom0057Coded := by decide +kernel
theorem atom0057Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (968550 : Int) atom0057Coded) := by
  have h := atom0057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0058 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0058 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0058 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0058_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (700670 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058Coded : CoefficientMerge.Poly := [(124, 1)]
theorem atom0058Coded_decode : atom0058 = SparsePolynomial.decodeCubic 9 atom0058Coded := by decide +kernel
theorem atom0058Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (700670 : Int) atom0058Coded) := by
  have h := atom0058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0059 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0059 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0059 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0059_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (874770 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059Coded : CoefficientMerge.Poly := [(125, 1)]
theorem atom0059Coded_decode : atom0059 = SparsePolynomial.decodeCubic 9 atom0059Coded := by decide +kernel
theorem atom0059Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (874770 : Int) atom0059Coded) := by
  have h := atom0059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0060 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0060 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0060 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0060_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (489240 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060Coded : CoefficientMerge.Poly := [(131, 1)]
theorem atom0060Coded_decode : atom0060 = SparsePolynomial.decodeCubic 9 atom0060Coded := by decide +kernel
theorem atom0060Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (489240 : Int) atom0060Coded) := by
  have h := atom0060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0061 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0061 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0061 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0061_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (975960 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061Coded : CoefficientMerge.Poly := [(132, 1)]
theorem atom0061Coded_decode : atom0061 = SparsePolynomial.decodeCubic 9 atom0061Coded := by decide +kernel
theorem atom0061Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (975960 : Int) atom0061Coded) := by
  have h := atom0061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0062 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0062 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0062 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0062_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (743780 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062Coded : CoefficientMerge.Poly := [(133, 1)]
theorem atom0062Coded_decode : atom0062 = SparsePolynomial.decodeCubic 9 atom0062Coded := by decide +kernel
theorem atom0062Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (743780 : Int) atom0062Coded) := by
  have h := atom0062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0063 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0063 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0063 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0063_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (978960 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063Coded : CoefficientMerge.Poly := [(134, 1)]
theorem atom0063Coded_decode : atom0063 = SparsePolynomial.decodeCubic 9 atom0063Coded := by decide +kernel
theorem atom0063Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (978960 : Int) atom0063Coded) := by
  have h := atom0063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0064 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0064 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0064 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0064_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436320 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064Coded : CoefficientMerge.Poly := [(141, 1)]
theorem atom0064Coded_decode : atom0064 = SparsePolynomial.decodeCubic 9 atom0064Coded := by decide +kernel
theorem atom0064Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (436320 : Int) atom0064Coded) := by
  have h := atom0064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0065 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0065 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0065 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0065_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (697890 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065Coded : CoefficientMerge.Poly := [(142, 1)]
theorem atom0065Coded_decode : atom0065 = SparsePolynomial.decodeCubic 9 atom0065Coded := by decide +kernel
theorem atom0065Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (697890 : Int) atom0065Coded) := by
  have h := atom0065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0066 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0066 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0066 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0066_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (989850 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066Coded : CoefficientMerge.Poly := [(143, 1)]
theorem atom0066Coded_decode : atom0066 = SparsePolynomial.decodeCubic 9 atom0066Coded := by decide +kernel
theorem atom0066Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (989850 : Int) atom0066Coded) := by
  have h := atom0066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0067 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0067 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0067 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0067_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179150 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067Coded : CoefficientMerge.Poly := [(151, 1)]
theorem atom0067Coded_decode : atom0067 = SparsePolynomial.decodeCubic 9 atom0067Coded := by decide +kernel
theorem atom0067Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (179150 : Int) atom0067Coded) := by
  have h := atom0067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0068 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0068 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0068 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0068_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (626340 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068Coded : CoefficientMerge.Poly := [(152, 1)]
theorem atom0068Coded_decode : atom0068 = SparsePolynomial.decodeCubic 9 atom0068Coded := by decide +kernel
theorem atom0068Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (626340 : Int) atom0068Coded) := by
  have h := atom0068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0069 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0069 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0069 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0069_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331830 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069Coded : CoefficientMerge.Poly := [(161, 1)]
theorem atom0069Coded_decode : atom0069 = SparsePolynomial.decodeCubic 9 atom0069Coded := by decide +kernel
theorem atom0069Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (331830 : Int) atom0069Coded) := by
  have h := atom0069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0070 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0070 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0070 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0070_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6480 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070Coded : CoefficientMerge.Poly := [(182, 1)]
theorem atom0070Coded_decode : atom0070 = SparsePolynomial.decodeCubic 9 atom0070Coded := by decide +kernel
theorem atom0070Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (6480 : Int) atom0070Coded) := by
  have h := atom0070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0071 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0071 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0071 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0071_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287280 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071Coded : CoefficientMerge.Poly := [(183, 1)]
theorem atom0071Coded_decode : atom0071 = SparsePolynomial.decodeCubic 9 atom0071Coded := by decide +kernel
theorem atom0071Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (287280 : Int) atom0071Coded) := by
  have h := atom0071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0072 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0072 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0072 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0072_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88560 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072Coded : CoefficientMerge.Poly := [(184, 1)]
theorem atom0072Coded_decode : atom0072 = SparsePolynomial.decodeCubic 9 atom0072Coded := by decide +kernel
theorem atom0072Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (88560 : Int) atom0072Coded) := by
  have h := atom0072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0073 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0073 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0073 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0073_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158760 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073Coded : CoefficientMerge.Poly := [(185, 1)]
theorem atom0073Coded_decode : atom0073 = SparsePolynomial.decodeCubic 9 atom0073Coded := by decide +kernel
theorem atom0073Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (158760 : Int) atom0073Coded) := by
  have h := atom0073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0074 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0074 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0074 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0074_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157680 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074Coded : CoefficientMerge.Poly := [(186, 1)]
theorem atom0074Coded_decode : atom0074 = SparsePolynomial.decodeCubic 9 atom0074Coded := by decide +kernel
theorem atom0074Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (157680 : Int) atom0074Coded) := by
  have h := atom0074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0075 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0075 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0075 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0075_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226800 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075Coded : CoefficientMerge.Poly := [(188, 1)]
theorem atom0075Coded_decode : atom0075 = SparsePolynomial.decodeCubic 9 atom0075Coded := by decide +kernel
theorem atom0075Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (226800 : Int) atom0075Coded) := by
  have h := atom0075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0076 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0076 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0076 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0076_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479520 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076Coded : CoefficientMerge.Poly := [(192, 1)]
theorem atom0076Coded_decode : atom0076 = SparsePolynomial.decodeCubic 9 atom0076Coded := by decide +kernel
theorem atom0076Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (479520 : Int) atom0076Coded) := by
  have h := atom0076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0077 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0077 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0077 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0077_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (671760 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077Coded : CoefficientMerge.Poly := [(193, 1)]
theorem atom0077Coded_decode : atom0077 = SparsePolynomial.decodeCubic 9 atom0077Coded := by decide +kernel
theorem atom0077Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (671760 : Int) atom0077Coded) := by
  have h := atom0077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0078 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0078 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0078 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0078_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (922320 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078Coded : CoefficientMerge.Poly := [(194, 1)]
theorem atom0078Coded_decode : atom0078 = SparsePolynomial.decodeCubic 9 atom0078Coded := by decide +kernel
theorem atom0078Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (922320 : Int) atom0078Coded) := by
  have h := atom0078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0079 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0079 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0079 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0079_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1030320 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079Coded : CoefficientMerge.Poly := [(195, 1)]
theorem atom0079Coded_decode : atom0079 = SparsePolynomial.decodeCubic 9 atom0079Coded := by decide +kernel
theorem atom0079Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1030320 : Int) atom0079Coded) := by
  have h := atom0079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block000 : CoefficientMerge.Poly := [(3, 120240), (4, 95040), (5, 69840), (6, 44640), (10, 27240), (11, 175680), (12, 481140), (13, 229160), (14, 126540), (15, 81540), (16, 45520), (20, 219600), (21, 731160), (22, 477000), (23, 313380), (24, 158040), (25, 139500), (26, 34200), (30, 508320), (31, 843120), (32, 804060), (33, 729360), (34, 344700), (35, 388080), (40, 382464), (41, 715680), (42, 812160), (43, 436500), (44, 544320), (50, 380880), (51, 894960), (52, 500580), (53, 470160), (60, 488880), (61, 592380), (62, 626400), (70, 60300), (71, 110700), (91, 360), (92, 11280), (93, 209940), (96, 1380), (101, 12960), (102, 538560), (103, 223280), (104, 334260), (105, 443520), (106, 404920), (107, 560400), (111, 475200), (112, 655960), (113, 892980), (114, 1075680), (115, 559400), (116, 745140), (121, 213356), (122, 591100), (123, 968550), (124, 700670), (125, 874770), (131, 489240), (132, 975960), (133, 743780), (134, 978960), (141, 436320), (142, 697890), (143, 989850), (151, 179150), (152, 626340), (161, 331830), (182, 6480), (183, 287280), (184, 88560), (185, 158760), (186, 157680), (188, 226800), (192, 479520), (193, 671760), (194, 922320), (195, 1030320)]
theorem block000_data : block000 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)))))))) := by decide +kernel
theorem block000_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) block000 := by
  rw [block000_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000Coded_nonneg g hg hA hB) (atom0001Coded_nonneg g hg hA hB)) (add_nonneg (atom0002Coded_nonneg g hg hA hB) (add_nonneg (atom0003Coded_nonneg g hg hA hB) (atom0004Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0005Coded_nonneg g hg hA hB) (atom0006Coded_nonneg g hg hA hB)) (add_nonneg (atom0007Coded_nonneg g hg hA hB) (add_nonneg (atom0008Coded_nonneg g hg hA hB) (atom0009Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0010Coded_nonneg g hg hA hB) (atom0011Coded_nonneg g hg hA hB)) (add_nonneg (atom0012Coded_nonneg g hg hA hB) (add_nonneg (atom0013Coded_nonneg g hg hA hB) (atom0014Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0015Coded_nonneg g hg hA hB) (atom0016Coded_nonneg g hg hA hB)) (add_nonneg (atom0017Coded_nonneg g hg hA hB) (add_nonneg (atom0018Coded_nonneg g hg hA hB) (atom0019Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0020Coded_nonneg g hg hA hB) (atom0021Coded_nonneg g hg hA hB)) (add_nonneg (atom0022Coded_nonneg g hg hA hB) (add_nonneg (atom0023Coded_nonneg g hg hA hB) (atom0024Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0025Coded_nonneg g hg hA hB) (atom0026Coded_nonneg g hg hA hB)) (add_nonneg (atom0027Coded_nonneg g hg hA hB) (add_nonneg (atom0028Coded_nonneg g hg hA hB) (atom0029Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0030Coded_nonneg g hg hA hB) (atom0031Coded_nonneg g hg hA hB)) (add_nonneg (atom0032Coded_nonneg g hg hA hB) (add_nonneg (atom0033Coded_nonneg g hg hA hB) (atom0034Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0035Coded_nonneg g hg hA hB) (atom0036Coded_nonneg g hg hA hB)) (add_nonneg (atom0037Coded_nonneg g hg hA hB) (add_nonneg (atom0038Coded_nonneg g hg hA hB) (atom0039Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0040Coded_nonneg g hg hA hB) (atom0041Coded_nonneg g hg hA hB)) (add_nonneg (atom0042Coded_nonneg g hg hA hB) (add_nonneg (atom0043Coded_nonneg g hg hA hB) (atom0044Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0045Coded_nonneg g hg hA hB) (atom0046Coded_nonneg g hg hA hB)) (add_nonneg (atom0047Coded_nonneg g hg hA hB) (add_nonneg (atom0048Coded_nonneg g hg hA hB) (atom0049Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0050Coded_nonneg g hg hA hB) (atom0051Coded_nonneg g hg hA hB)) (add_nonneg (atom0052Coded_nonneg g hg hA hB) (add_nonneg (atom0053Coded_nonneg g hg hA hB) (atom0054Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0055Coded_nonneg g hg hA hB) (atom0056Coded_nonneg g hg hA hB)) (add_nonneg (atom0057Coded_nonneg g hg hA hB) (add_nonneg (atom0058Coded_nonneg g hg hA hB) (atom0059Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0060Coded_nonneg g hg hA hB) (atom0061Coded_nonneg g hg hA hB)) (add_nonneg (atom0062Coded_nonneg g hg hA hB) (add_nonneg (atom0063Coded_nonneg g hg hA hB) (atom0064Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0065Coded_nonneg g hg hA hB) (atom0066Coded_nonneg g hg hA hB)) (add_nonneg (atom0067Coded_nonneg g hg hA hB) (add_nonneg (atom0068Coded_nonneg g hg hA hB) (atom0069Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0070Coded_nonneg g hg hA hB) (atom0071Coded_nonneg g hg hA hB)) (add_nonneg (atom0072Coded_nonneg g hg hA hB) (add_nonneg (atom0073Coded_nonneg g hg hA hB) (atom0074Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0075Coded_nonneg g hg hA hB) (atom0076Coded_nonneg g hg hA hB)) (add_nonneg (atom0077Coded_nonneg g hg hA hB) (add_nonneg (atom0078Coded_nonneg g hg hA hB) (atom0079Coded_nonneg g hg hA hB))))))))

end APPT.Finite9
