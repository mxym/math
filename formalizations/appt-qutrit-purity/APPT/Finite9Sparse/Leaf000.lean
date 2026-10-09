-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0000 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0000 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0000 = ((g 0) * (g 0) * (g 3)) := by
  norm_num [atom0000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0000_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120240 : Int) atom0000) := by
  rw [SparsePolynomial.eval_scale, eval_atom0000]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 0) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0000Coded : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 1))]
theorem atom0000Coded_decode : atom0000 = SparsePolynomial.decodeCubic 9 atom0000Coded := by decide +kernel
theorem atom0000Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (120240 : Int) atom0000Coded) := by
  have h := atom0000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0001 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0001 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0001 = ((g 0) * (g 0) * (g 4)) := by
  norm_num [atom0001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0001_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95040 : Int) atom0001) := by
  rw [SparsePolynomial.eval_scale, eval_atom0001]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 0) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0001Coded : CoefficientMerge.Poly := [(nat_lit 4, Int.ofNat (nat_lit 1))]
theorem atom0001Coded_decode : atom0001 = SparsePolynomial.decodeCubic 9 atom0001Coded := by decide +kernel
theorem atom0001Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (95040 : Int) atom0001Coded) := by
  have h := atom0001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0002 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0002 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0002 = ((g 0) * (g 0) * (g 5)) := by
  norm_num [atom0002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0002_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69840 : Int) atom0002) := by
  rw [SparsePolynomial.eval_scale, eval_atom0002]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 0) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0002Coded : CoefficientMerge.Poly := [(nat_lit 5, Int.ofNat (nat_lit 1))]
theorem atom0002Coded_decode : atom0002 = SparsePolynomial.decodeCubic 9 atom0002Coded := by decide +kernel
theorem atom0002Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (69840 : Int) atom0002Coded) := by
  have h := atom0002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0003 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0003 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0003 = ((g 0) * (g 0) * (g 6)) := by
  norm_num [atom0003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0003_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44640 : Int) atom0003) := by
  rw [SparsePolynomial.eval_scale, eval_atom0003]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 0) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0003Coded : CoefficientMerge.Poly := [(nat_lit 6, Int.ofNat (nat_lit 1))]
theorem atom0003Coded_decode : atom0003 = SparsePolynomial.decodeCubic 9 atom0003Coded := by decide +kernel
theorem atom0003Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (44640 : Int) atom0003Coded) := by
  have h := atom0003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0004 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 1], Int.ofNat (nat_lit 1))]
theorem eval_atom0004 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0004 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0004_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27240 : Int) atom0004) := by
  rw [SparsePolynomial.eval_scale, eval_atom0004]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0004Coded : CoefficientMerge.Poly := [(nat_lit 10, Int.ofNat (nat_lit 1))]
theorem atom0004Coded_decode : atom0004 = SparsePolynomial.decodeCubic 9 atom0004Coded := by decide +kernel
theorem atom0004Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (27240 : Int) atom0004Coded) := by
  have h := atom0004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0005 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1))]
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
def atom0005Coded : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 1))]
theorem atom0005Coded_decode : atom0005 = SparsePolynomial.decodeCubic 9 atom0005Coded := by decide +kernel
theorem atom0005Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (175680 : Int) atom0005Coded) := by
  have h := atom0005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0006 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1))]
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
def atom0006Coded : CoefficientMerge.Poly := [(nat_lit 12, Int.ofNat (nat_lit 1))]
theorem atom0006Coded_decode : atom0006 = SparsePolynomial.decodeCubic 9 atom0006Coded := by decide +kernel
theorem atom0006Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (481140 : Int) atom0006Coded) := by
  have h := atom0006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0007 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0007Coded : CoefficientMerge.Poly := [(nat_lit 13, Int.ofNat (nat_lit 1))]
theorem atom0007Coded_decode : atom0007 = SparsePolynomial.decodeCubic 9 atom0007Coded := by decide +kernel
theorem atom0007Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (229160 : Int) atom0007Coded) := by
  have h := atom0007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0008 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0008Coded : CoefficientMerge.Poly := [(nat_lit 14, Int.ofNat (nat_lit 1))]
theorem atom0008Coded_decode : atom0008 = SparsePolynomial.decodeCubic 9 atom0008Coded := by decide +kernel
theorem atom0008Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (126540 : Int) atom0008Coded) := by
  have h := atom0008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0009 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0009Coded : CoefficientMerge.Poly := [(nat_lit 15, Int.ofNat (nat_lit 1))]
theorem atom0009Coded_decode : atom0009 = SparsePolynomial.decodeCubic 9 atom0009Coded := by decide +kernel
theorem atom0009Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (81540 : Int) atom0009Coded) := by
  have h := atom0009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0010 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0010Coded : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 1))]
theorem atom0010Coded_decode : atom0010 = SparsePolynomial.decodeCubic 9 atom0010Coded := by decide +kernel
theorem atom0010Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (45520 : Int) atom0010Coded) := by
  have h := atom0010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0011 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0011 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0011 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0011_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219600 : Int) atom0011) := by
  rw [SparsePolynomial.eval_scale, eval_atom0011]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0011Coded : CoefficientMerge.Poly := [(nat_lit 20, Int.ofNat (nat_lit 1))]
theorem atom0011Coded_decode : atom0011 = SparsePolynomial.decodeCubic 9 atom0011Coded := by decide +kernel
theorem atom0011Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (219600 : Int) atom0011Coded) := by
  have h := atom0011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0012 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
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
def atom0012Coded : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 1))]
theorem atom0012Coded_decode : atom0012 = SparsePolynomial.decodeCubic 9 atom0012Coded := by decide +kernel
theorem atom0012Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (731160 : Int) atom0012Coded) := by
  have h := atom0012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0013 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0013Coded : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 1))]
theorem atom0013Coded_decode : atom0013 = SparsePolynomial.decodeCubic 9 atom0013Coded := by decide +kernel
theorem atom0013Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (477000 : Int) atom0013Coded) := by
  have h := atom0013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0014 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0014Coded : CoefficientMerge.Poly := [(nat_lit 23, Int.ofNat (nat_lit 1))]
theorem atom0014Coded_decode : atom0014 = SparsePolynomial.decodeCubic 9 atom0014Coded := by decide +kernel
theorem atom0014Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (313380 : Int) atom0014Coded) := by
  have h := atom0014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0015 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0015Coded : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 1))]
theorem atom0015Coded_decode : atom0015 = SparsePolynomial.decodeCubic 9 atom0015Coded := by decide +kernel
theorem atom0015Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (158040 : Int) atom0015Coded) := by
  have h := atom0015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0016 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0016Coded : CoefficientMerge.Poly := [(nat_lit 25, Int.ofNat (nat_lit 1))]
theorem atom0016Coded_decode : atom0016 = SparsePolynomial.decodeCubic 9 atom0016Coded := by decide +kernel
theorem atom0016Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (139500 : Int) atom0016Coded) := by
  have h := atom0016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0017 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0017Coded : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 1))]
theorem atom0017Coded_decode : atom0017 = SparsePolynomial.decodeCubic 9 atom0017Coded := by decide +kernel
theorem atom0017Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (34200 : Int) atom0017Coded) := by
  have h := atom0017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0018 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0018 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (508320 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018Coded : CoefficientMerge.Poly := [(nat_lit 30, Int.ofNat (nat_lit 1))]
theorem atom0018Coded_decode : atom0018 = SparsePolynomial.decodeCubic 9 atom0018Coded := by decide +kernel
theorem atom0018Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (508320 : Int) atom0018Coded) := by
  have h := atom0018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0019 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0019Coded : CoefficientMerge.Poly := [(nat_lit 31, Int.ofNat (nat_lit 1))]
theorem atom0019Coded_decode : atom0019 = SparsePolynomial.decodeCubic 9 atom0019Coded := by decide +kernel
theorem atom0019Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (843120 : Int) atom0019Coded) := by
  have h := atom0019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0020 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0020Coded : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 1))]
theorem atom0020Coded_decode : atom0020 = SparsePolynomial.decodeCubic 9 atom0020Coded := by decide +kernel
theorem atom0020Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (804060 : Int) atom0020Coded) := by
  have h := atom0020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0021 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0021Coded : CoefficientMerge.Poly := [(nat_lit 33, Int.ofNat (nat_lit 1))]
theorem atom0021Coded_decode : atom0021 = SparsePolynomial.decodeCubic 9 atom0021Coded := by decide +kernel
theorem atom0021Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (729360 : Int) atom0021Coded) := by
  have h := atom0021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0022 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0022Coded : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 1))]
theorem atom0022Coded_decode : atom0022 = SparsePolynomial.decodeCubic 9 atom0022Coded := by decide +kernel
theorem atom0022Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (344700 : Int) atom0022Coded) := by
  have h := atom0022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0023 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0023Coded : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 1))]
theorem atom0023Coded_decode : atom0023 = SparsePolynomial.decodeCubic 9 atom0023Coded := by decide +kernel
theorem atom0023Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (388080 : Int) atom0023Coded) := by
  have h := atom0023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0024 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0024 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382464 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024Coded : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 1))]
theorem atom0024Coded_decode : atom0024 = SparsePolynomial.decodeCubic 9 atom0024Coded := by decide +kernel
theorem atom0024Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (382464 : Int) atom0024Coded) := by
  have h := atom0024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0025 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0025Coded : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 1))]
theorem atom0025Coded_decode : atom0025 = SparsePolynomial.decodeCubic 9 atom0025Coded := by decide +kernel
theorem atom0025Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (715680 : Int) atom0025Coded) := by
  have h := atom0025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0026 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0026Coded : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 1))]
theorem atom0026Coded_decode : atom0026 = SparsePolynomial.decodeCubic 9 atom0026Coded := by decide +kernel
theorem atom0026Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (812160 : Int) atom0026Coded) := by
  have h := atom0026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0027 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0027Coded : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 1))]
theorem atom0027Coded_decode : atom0027 = SparsePolynomial.decodeCubic 9 atom0027Coded := by decide +kernel
theorem atom0027Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (436500 : Int) atom0027Coded) := by
  have h := atom0027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0028 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0028Coded : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 1))]
theorem atom0028Coded_decode : atom0028 = SparsePolynomial.decodeCubic 9 atom0028Coded := by decide +kernel
theorem atom0028Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (544320 : Int) atom0028Coded) := by
  have h := atom0028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0029 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0029 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380880 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029Coded : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 1))]
theorem atom0029Coded_decode : atom0029 = SparsePolynomial.decodeCubic 9 atom0029Coded := by decide +kernel
theorem atom0029Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (380880 : Int) atom0029Coded) := by
  have h := atom0029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0030 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0030Coded : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 1))]
theorem atom0030Coded_decode : atom0030 = SparsePolynomial.decodeCubic 9 atom0030Coded := by decide +kernel
theorem atom0030Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (894960 : Int) atom0030Coded) := by
  have h := atom0030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0031 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0031Coded : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 1))]
theorem atom0031Coded_decode : atom0031 = SparsePolynomial.decodeCubic 9 atom0031Coded := by decide +kernel
theorem atom0031Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (500580 : Int) atom0031Coded) := by
  have h := atom0031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0032 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0032Coded : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 1))]
theorem atom0032Coded_decode : atom0032 = SparsePolynomial.decodeCubic 9 atom0032Coded := by decide +kernel
theorem atom0032Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (470160 : Int) atom0032Coded) := by
  have h := atom0032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0033 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0033 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488880 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033Coded : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1))]
theorem atom0033Coded_decode : atom0033 = SparsePolynomial.decodeCubic 9 atom0033Coded := by decide +kernel
theorem atom0033Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (488880 : Int) atom0033Coded) := by
  have h := atom0033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0034 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0034Coded : CoefficientMerge.Poly := [(nat_lit 61, Int.ofNat (nat_lit 1))]
theorem atom0034Coded_decode : atom0034 = SparsePolynomial.decodeCubic 9 atom0034Coded := by decide +kernel
theorem atom0034Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (592380 : Int) atom0034Coded) := by
  have h := atom0034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0035 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0035Coded : CoefficientMerge.Poly := [(nat_lit 62, Int.ofNat (nat_lit 1))]
theorem atom0035Coded_decode : atom0035 = SparsePolynomial.decodeCubic 9 atom0035Coded := by decide +kernel
theorem atom0035Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (626400 : Int) atom0035Coded) := by
  have h := atom0035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0036 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0036 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60300 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036Coded : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 1))]
theorem atom0036Coded_decode : atom0036 = SparsePolynomial.decodeCubic 9 atom0036Coded := by decide +kernel
theorem atom0036Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (60300 : Int) atom0036Coded) := by
  have h := atom0036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0037 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0037Coded : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 1))]
theorem atom0037Coded_decode : atom0037 = SparsePolynomial.decodeCubic 9 atom0037Coded := by decide +kernel
theorem atom0037Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (110700 : Int) atom0037Coded) := by
  have h := atom0037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0038 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 1], Int.ofNat (nat_lit 1))]
theorem eval_atom0038 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = ((g 1) * (g 1) * (g 1)) := by
  norm_num [atom0038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 1) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038Coded : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 1))]
theorem atom0038Coded_decode : atom0038 = SparsePolynomial.decodeCubic 9 atom0038Coded := by decide +kernel
theorem atom0038Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (360 : Int) atom0038Coded) := by
  have h := atom0038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0039 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0039 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0039 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0039_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11280 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039Coded : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 1))]
theorem atom0039Coded_decode : atom0039 = SparsePolynomial.decodeCubic 9 atom0039Coded := by decide +kernel
theorem atom0039Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (11280 : Int) atom0039Coded) := by
  have h := atom0039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0040 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0040 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0040 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0040_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (209940 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040Coded : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 1))]
theorem atom0040Coded_decode : atom0040 = SparsePolynomial.decodeCubic 9 atom0040Coded := by decide +kernel
theorem atom0040Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (209940 : Int) atom0040Coded) := by
  have h := atom0040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0041 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0041 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0041 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0041_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1380 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041Coded : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 1))]
theorem atom0041Coded_decode : atom0041 = SparsePolynomial.decodeCubic 9 atom0041Coded := by decide +kernel
theorem atom0041Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1380 : Int) atom0041Coded) := by
  have h := atom0041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0042 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0042 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0042 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0042_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12960 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042Coded : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 1))]
theorem atom0042Coded_decode : atom0042 = SparsePolynomial.decodeCubic 9 atom0042Coded := by decide +kernel
theorem atom0042Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (12960 : Int) atom0042Coded) := by
  have h := atom0042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0043 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
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
def atom0043Coded : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 1))]
theorem atom0043Coded_decode : atom0043 = SparsePolynomial.decodeCubic 9 atom0043Coded := by decide +kernel
theorem atom0043Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (538560 : Int) atom0043Coded) := by
  have h := atom0043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0044 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0044Coded : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 1))]
theorem atom0044Coded_decode : atom0044 = SparsePolynomial.decodeCubic 9 atom0044Coded := by decide +kernel
theorem atom0044Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (223280 : Int) atom0044Coded) := by
  have h := atom0044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0045 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0045Coded : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 1))]
theorem atom0045Coded_decode : atom0045 = SparsePolynomial.decodeCubic 9 atom0045Coded := by decide +kernel
theorem atom0045Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (334260 : Int) atom0045Coded) := by
  have h := atom0045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0046 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0046Coded : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 1))]
theorem atom0046Coded_decode : atom0046 = SparsePolynomial.decodeCubic 9 atom0046Coded := by decide +kernel
theorem atom0046Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (443520 : Int) atom0046Coded) := by
  have h := atom0046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0047 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0047Coded : CoefficientMerge.Poly := [(nat_lit 106, Int.ofNat (nat_lit 1))]
theorem atom0047Coded_decode : atom0047 = SparsePolynomial.decodeCubic 9 atom0047Coded := by decide +kernel
theorem atom0047Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (404920 : Int) atom0047Coded) := by
  have h := atom0047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0048 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0048Coded : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 1))]
theorem atom0048Coded_decode : atom0048 = SparsePolynomial.decodeCubic 9 atom0048Coded := by decide +kernel
theorem atom0048Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (560400 : Int) atom0048Coded) := by
  have h := atom0048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0049 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0049 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0049 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0049_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475200 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049Coded : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 1))]
theorem atom0049Coded_decode : atom0049 = SparsePolynomial.decodeCubic 9 atom0049Coded := by decide +kernel
theorem atom0049Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (475200 : Int) atom0049Coded) := by
  have h := atom0049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0050 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0050Coded : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 1))]
theorem atom0050Coded_decode : atom0050 = SparsePolynomial.decodeCubic 9 atom0050Coded := by decide +kernel
theorem atom0050Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (655960 : Int) atom0050Coded) := by
  have h := atom0050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0051 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0051Coded : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 1))]
theorem atom0051Coded_decode : atom0051 = SparsePolynomial.decodeCubic 9 atom0051Coded := by decide +kernel
theorem atom0051Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (892980 : Int) atom0051Coded) := by
  have h := atom0051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0052 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0052Coded : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1))]
theorem atom0052Coded_decode : atom0052 = SparsePolynomial.decodeCubic 9 atom0052Coded := by decide +kernel
theorem atom0052Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1075680 : Int) atom0052Coded) := by
  have h := atom0052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0053 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0053Coded : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 1))]
theorem atom0053Coded_decode : atom0053 = SparsePolynomial.decodeCubic 9 atom0053Coded := by decide +kernel
theorem atom0053Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (559400 : Int) atom0053Coded) := by
  have h := atom0053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0054 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0054Coded : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 1))]
theorem atom0054Coded_decode : atom0054 = SparsePolynomial.decodeCubic 9 atom0054Coded := by decide +kernel
theorem atom0054Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (745140 : Int) atom0054Coded) := by
  have h := atom0054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0055 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0055 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0055 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0055_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213356 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055Coded : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 1))]
theorem atom0055Coded_decode : atom0055 = SparsePolynomial.decodeCubic 9 atom0055Coded := by decide +kernel
theorem atom0055Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (213356 : Int) atom0055Coded) := by
  have h := atom0055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0056 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0056Coded : CoefficientMerge.Poly := [(nat_lit 122, Int.ofNat (nat_lit 1))]
theorem atom0056Coded_decode : atom0056 = SparsePolynomial.decodeCubic 9 atom0056Coded := by decide +kernel
theorem atom0056Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (591100 : Int) atom0056Coded) := by
  have h := atom0056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0057 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0057Coded : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 1))]
theorem atom0057Coded_decode : atom0057 = SparsePolynomial.decodeCubic 9 atom0057Coded := by decide +kernel
theorem atom0057Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (968550 : Int) atom0057Coded) := by
  have h := atom0057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0058 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0058Coded : CoefficientMerge.Poly := [(nat_lit 124, Int.ofNat (nat_lit 1))]
theorem atom0058Coded_decode : atom0058 = SparsePolynomial.decodeCubic 9 atom0058Coded := by decide +kernel
theorem atom0058Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (700670 : Int) atom0058Coded) := by
  have h := atom0058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0059 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0059Coded : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 1))]
theorem atom0059Coded_decode : atom0059 = SparsePolynomial.decodeCubic 9 atom0059Coded := by decide +kernel
theorem atom0059Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (874770 : Int) atom0059Coded) := by
  have h := atom0059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0060 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0060 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0060 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0060_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (489240 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060Coded : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 1))]
theorem atom0060Coded_decode : atom0060 = SparsePolynomial.decodeCubic 9 atom0060Coded := by decide +kernel
theorem atom0060Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (489240 : Int) atom0060Coded) := by
  have h := atom0060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0061 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0061Coded : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 1))]
theorem atom0061Coded_decode : atom0061 = SparsePolynomial.decodeCubic 9 atom0061Coded := by decide +kernel
theorem atom0061Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (975960 : Int) atom0061Coded) := by
  have h := atom0061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0062 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0062Coded : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 1))]
theorem atom0062Coded_decode : atom0062 = SparsePolynomial.decodeCubic 9 atom0062Coded := by decide +kernel
theorem atom0062Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (743780 : Int) atom0062Coded) := by
  have h := atom0062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0063 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0063Coded : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 1))]
theorem atom0063Coded_decode : atom0063 = SparsePolynomial.decodeCubic 9 atom0063Coded := by decide +kernel
theorem atom0063Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (978960 : Int) atom0063Coded) := by
  have h := atom0063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0064 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0064 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0064 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0064_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436320 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064Coded : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 1))]
theorem atom0064Coded_decode : atom0064 = SparsePolynomial.decodeCubic 9 atom0064Coded := by decide +kernel
theorem atom0064Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (436320 : Int) atom0064Coded) := by
  have h := atom0064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0065 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
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
def atom0065Coded : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 1))]
theorem atom0065Coded_decode : atom0065 = SparsePolynomial.decodeCubic 9 atom0065Coded := by decide +kernel
theorem atom0065Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (697890 : Int) atom0065Coded) := by
  have h := atom0065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0066 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0066Coded : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 1))]
theorem atom0066Coded_decode : atom0066 = SparsePolynomial.decodeCubic 9 atom0066Coded := by decide +kernel
theorem atom0066Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (989850 : Int) atom0066Coded) := by
  have h := atom0066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0067 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0067 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0067 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0067_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179150 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067Coded : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 1))]
theorem atom0067Coded_decode : atom0067 = SparsePolynomial.decodeCubic 9 atom0067Coded := by decide +kernel
theorem atom0067Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (179150 : Int) atom0067Coded) := by
  have h := atom0067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0068 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
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
def atom0068Coded : CoefficientMerge.Poly := [(nat_lit 152, Int.ofNat (nat_lit 1))]
theorem atom0068Coded_decode : atom0068 = SparsePolynomial.decodeCubic 9 atom0068Coded := by decide +kernel
theorem atom0068Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (626340 : Int) atom0068Coded) := by
  have h := atom0068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0069 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0069 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0069 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0069_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331830 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069Coded : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 1))]
theorem atom0069Coded_decode : atom0069 = SparsePolynomial.decodeCubic 9 atom0069Coded := by decide +kernel
theorem atom0069Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (331830 : Int) atom0069Coded) := by
  have h := atom0069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0070 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0070 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0070 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0070_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6480 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070Coded : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 1))]
theorem atom0070Coded_decode : atom0070 = SparsePolynomial.decodeCubic 9 atom0070Coded := by decide +kernel
theorem atom0070Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (6480 : Int) atom0070Coded) := by
  have h := atom0070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0071 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0071 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0071 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0071_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287280 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071Coded : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 1))]
theorem atom0071Coded_decode : atom0071 = SparsePolynomial.decodeCubic 9 atom0071Coded := by decide +kernel
theorem atom0071Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (287280 : Int) atom0071Coded) := by
  have h := atom0071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0072 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0072 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0072 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0072_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88560 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072Coded : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 1))]
theorem atom0072Coded_decode : atom0072 = SparsePolynomial.decodeCubic 9 atom0072Coded := by decide +kernel
theorem atom0072Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (88560 : Int) atom0072Coded) := by
  have h := atom0072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0073 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0073 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0073 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0073_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158760 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073Coded : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 1))]
theorem atom0073Coded_decode : atom0073 = SparsePolynomial.decodeCubic 9 atom0073Coded := by decide +kernel
theorem atom0073Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (158760 : Int) atom0073Coded) := by
  have h := atom0073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0074 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0074 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0074 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0074_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157680 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074Coded : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 1))]
theorem atom0074Coded_decode : atom0074 = SparsePolynomial.decodeCubic 9 atom0074Coded := by decide +kernel
theorem atom0074Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (157680 : Int) atom0074Coded) := by
  have h := atom0074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0075 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0075 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0075 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0075_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226800 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075Coded : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 1))]
theorem atom0075Coded_decode : atom0075 = SparsePolynomial.decodeCubic 9 atom0075Coded := by decide +kernel
theorem atom0075Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (226800 : Int) atom0075Coded) := by
  have h := atom0075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0076 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0076 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0076 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0076_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479520 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076Coded : CoefficientMerge.Poly := [(nat_lit 192, Int.ofNat (nat_lit 1))]
theorem atom0076Coded_decode : atom0076 = SparsePolynomial.decodeCubic 9 atom0076Coded := by decide +kernel
theorem atom0076Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (479520 : Int) atom0076Coded) := by
  have h := atom0076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0077 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
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
def atom0077Coded : CoefficientMerge.Poly := [(nat_lit 193, Int.ofNat (nat_lit 1))]
theorem atom0077Coded_decode : atom0077 = SparsePolynomial.decodeCubic 9 atom0077Coded := by decide +kernel
theorem atom0077Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (671760 : Int) atom0077Coded) := by
  have h := atom0077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0078 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
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
def atom0078Coded : CoefficientMerge.Poly := [(nat_lit 194, Int.ofNat (nat_lit 1))]
theorem atom0078Coded_decode : atom0078 = SparsePolynomial.decodeCubic 9 atom0078Coded := by decide +kernel
theorem atom0078Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (922320 : Int) atom0078Coded) := by
  have h := atom0078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0079 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
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
def atom0079Coded : CoefficientMerge.Poly := [(nat_lit 195, Int.ofNat (nat_lit 1))]
theorem atom0079Coded_decode : atom0079 = SparsePolynomial.decodeCubic 9 atom0079Coded := by decide +kernel
theorem atom0079Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1030320 : Int) atom0079Coded) := by
  have h := atom0079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block000 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540)), (nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120)), (nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880)), (nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280)), (nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200)), (nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770)), (nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830)), (nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
def block000_data_flat000 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240))]
theorem block000_data_flat000_step : block000_data_flat000 = (CoefficientMerge.scale (120240 : Int) atom0000Coded) := by decide +kernel
theorem block000_data_flat000_original : block000_data_flat000 = (CoefficientMerge.scale (120240 : Int) atom0000Coded) := by
  rw [block000_data_flat000_step]
def block000_data_flat001 : CoefficientMerge.Poly := [(nat_lit 4, Int.ofNat (nat_lit 95040))]
theorem block000_data_flat001_step : block000_data_flat001 = (CoefficientMerge.scale (95040 : Int) atom0001Coded) := by decide +kernel
theorem block000_data_flat001_original : block000_data_flat001 = (CoefficientMerge.scale (95040 : Int) atom0001Coded) := by
  rw [block000_data_flat001_step]
def block000_data_flat002 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040))]
theorem block000_data_flat002_step : block000_data_flat002 = (CoefficientMerge.fastMerge block000_data_flat000 block000_data_flat001) := by decide +kernel
theorem block000_data_flat002_original : block000_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) := by
  rw [block000_data_flat002_step, block000_data_flat000_original, block000_data_flat001_original]
def block000_data_flat003 : CoefficientMerge.Poly := [(nat_lit 5, Int.ofNat (nat_lit 69840))]
theorem block000_data_flat003_step : block000_data_flat003 = (CoefficientMerge.scale (69840 : Int) atom0002Coded) := by decide +kernel
theorem block000_data_flat003_original : block000_data_flat003 = (CoefficientMerge.scale (69840 : Int) atom0002Coded) := by
  rw [block000_data_flat003_step]
def block000_data_flat004 : CoefficientMerge.Poly := [(nat_lit 6, Int.ofNat (nat_lit 44640))]
theorem block000_data_flat004_step : block000_data_flat004 = (CoefficientMerge.scale (44640 : Int) atom0003Coded) := by decide +kernel
theorem block000_data_flat004_original : block000_data_flat004 = (CoefficientMerge.scale (44640 : Int) atom0003Coded) := by
  rw [block000_data_flat004_step]
def block000_data_flat005 : CoefficientMerge.Poly := [(nat_lit 10, Int.ofNat (nat_lit 27240))]
theorem block000_data_flat005_step : block000_data_flat005 = (CoefficientMerge.scale (27240 : Int) atom0004Coded) := by decide +kernel
theorem block000_data_flat005_original : block000_data_flat005 = (CoefficientMerge.scale (27240 : Int) atom0004Coded) := by
  rw [block000_data_flat005_step]
def block000_data_flat006 : CoefficientMerge.Poly := [(nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240))]
theorem block000_data_flat006_step : block000_data_flat006 = (CoefficientMerge.fastMerge block000_data_flat004 block000_data_flat005) := by decide +kernel
theorem block000_data_flat006_original : block000_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)) := by
  rw [block000_data_flat006_step, block000_data_flat004_original, block000_data_flat005_original]
def block000_data_flat007 : CoefficientMerge.Poly := [(nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240))]
theorem block000_data_flat007_step : block000_data_flat007 = (CoefficientMerge.fastMerge block000_data_flat003 block000_data_flat006) := by decide +kernel
theorem block000_data_flat007_original : block000_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded))) := by
  rw [block000_data_flat007_step, block000_data_flat003_original, block000_data_flat006_original]
def block000_data_flat008 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240))]
theorem block000_data_flat008_step : block000_data_flat008 = (CoefficientMerge.fastMerge block000_data_flat002 block000_data_flat007) := by decide +kernel
theorem block000_data_flat008_original : block000_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) := by
  rw [block000_data_flat008_step, block000_data_flat002_original, block000_data_flat007_original]
def block000_data_flat009 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 175680))]
theorem block000_data_flat009_step : block000_data_flat009 = (CoefficientMerge.scale (175680 : Int) atom0005Coded) := by decide +kernel
theorem block000_data_flat009_original : block000_data_flat009 = (CoefficientMerge.scale (175680 : Int) atom0005Coded) := by
  rw [block000_data_flat009_step]
def block000_data_flat010 : CoefficientMerge.Poly := [(nat_lit 12, Int.ofNat (nat_lit 481140))]
theorem block000_data_flat010_step : block000_data_flat010 = (CoefficientMerge.scale (481140 : Int) atom0006Coded) := by decide +kernel
theorem block000_data_flat010_original : block000_data_flat010 = (CoefficientMerge.scale (481140 : Int) atom0006Coded) := by
  rw [block000_data_flat010_step]
def block000_data_flat011 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140))]
theorem block000_data_flat011_step : block000_data_flat011 = (CoefficientMerge.fastMerge block000_data_flat009 block000_data_flat010) := by decide +kernel
theorem block000_data_flat011_original : block000_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) := by
  rw [block000_data_flat011_step, block000_data_flat009_original, block000_data_flat010_original]
def block000_data_flat012 : CoefficientMerge.Poly := [(nat_lit 13, Int.ofNat (nat_lit 229160))]
theorem block000_data_flat012_step : block000_data_flat012 = (CoefficientMerge.scale (229160 : Int) atom0007Coded) := by decide +kernel
theorem block000_data_flat012_original : block000_data_flat012 = (CoefficientMerge.scale (229160 : Int) atom0007Coded) := by
  rw [block000_data_flat012_step]
def block000_data_flat013 : CoefficientMerge.Poly := [(nat_lit 14, Int.ofNat (nat_lit 126540))]
theorem block000_data_flat013_step : block000_data_flat013 = (CoefficientMerge.scale (126540 : Int) atom0008Coded) := by decide +kernel
theorem block000_data_flat013_original : block000_data_flat013 = (CoefficientMerge.scale (126540 : Int) atom0008Coded) := by
  rw [block000_data_flat013_step]
def block000_data_flat014 : CoefficientMerge.Poly := [(nat_lit 15, Int.ofNat (nat_lit 81540))]
theorem block000_data_flat014_step : block000_data_flat014 = (CoefficientMerge.scale (81540 : Int) atom0009Coded) := by decide +kernel
theorem block000_data_flat014_original : block000_data_flat014 = (CoefficientMerge.scale (81540 : Int) atom0009Coded) := by
  rw [block000_data_flat014_step]
def block000_data_flat015 : CoefficientMerge.Poly := [(nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540))]
theorem block000_data_flat015_step : block000_data_flat015 = (CoefficientMerge.fastMerge block000_data_flat013 block000_data_flat014) := by decide +kernel
theorem block000_data_flat015_original : block000_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded)) := by
  rw [block000_data_flat015_step, block000_data_flat013_original, block000_data_flat014_original]
def block000_data_flat016 : CoefficientMerge.Poly := [(nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540))]
theorem block000_data_flat016_step : block000_data_flat016 = (CoefficientMerge.fastMerge block000_data_flat012 block000_data_flat015) := by decide +kernel
theorem block000_data_flat016_original : block000_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))) := by
  rw [block000_data_flat016_step, block000_data_flat012_original, block000_data_flat015_original]
def block000_data_flat017 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540))]
theorem block000_data_flat017_step : block000_data_flat017 = (CoefficientMerge.fastMerge block000_data_flat011 block000_data_flat016) := by decide +kernel
theorem block000_data_flat017_original : block000_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded)))) := by
  rw [block000_data_flat017_step, block000_data_flat011_original, block000_data_flat016_original]
def block000_data_flat018 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540))]
theorem block000_data_flat018_step : block000_data_flat018 = (CoefficientMerge.fastMerge block000_data_flat008 block000_data_flat017) := by decide +kernel
theorem block000_data_flat018_original : block000_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) := by
  rw [block000_data_flat018_step, block000_data_flat008_original, block000_data_flat017_original]
def block000_data_flat019 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 45520))]
theorem block000_data_flat019_step : block000_data_flat019 = (CoefficientMerge.scale (45520 : Int) atom0010Coded) := by decide +kernel
theorem block000_data_flat019_original : block000_data_flat019 = (CoefficientMerge.scale (45520 : Int) atom0010Coded) := by
  rw [block000_data_flat019_step]
def block000_data_flat020 : CoefficientMerge.Poly := [(nat_lit 20, Int.ofNat (nat_lit 219600))]
theorem block000_data_flat020_step : block000_data_flat020 = (CoefficientMerge.scale (219600 : Int) atom0011Coded) := by decide +kernel
theorem block000_data_flat020_original : block000_data_flat020 = (CoefficientMerge.scale (219600 : Int) atom0011Coded) := by
  rw [block000_data_flat020_step]
def block000_data_flat021 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600))]
theorem block000_data_flat021_step : block000_data_flat021 = (CoefficientMerge.fastMerge block000_data_flat019 block000_data_flat020) := by decide +kernel
theorem block000_data_flat021_original : block000_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) := by
  rw [block000_data_flat021_step, block000_data_flat019_original, block000_data_flat020_original]
def block000_data_flat022 : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 731160))]
theorem block000_data_flat022_step : block000_data_flat022 = (CoefficientMerge.scale (731160 : Int) atom0012Coded) := by decide +kernel
theorem block000_data_flat022_original : block000_data_flat022 = (CoefficientMerge.scale (731160 : Int) atom0012Coded) := by
  rw [block000_data_flat022_step]
def block000_data_flat023 : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 477000))]
theorem block000_data_flat023_step : block000_data_flat023 = (CoefficientMerge.scale (477000 : Int) atom0013Coded) := by decide +kernel
theorem block000_data_flat023_original : block000_data_flat023 = (CoefficientMerge.scale (477000 : Int) atom0013Coded) := by
  rw [block000_data_flat023_step]
def block000_data_flat024 : CoefficientMerge.Poly := [(nat_lit 23, Int.ofNat (nat_lit 313380))]
theorem block000_data_flat024_step : block000_data_flat024 = (CoefficientMerge.scale (313380 : Int) atom0014Coded) := by decide +kernel
theorem block000_data_flat024_original : block000_data_flat024 = (CoefficientMerge.scale (313380 : Int) atom0014Coded) := by
  rw [block000_data_flat024_step]
def block000_data_flat025 : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380))]
theorem block000_data_flat025_step : block000_data_flat025 = (CoefficientMerge.fastMerge block000_data_flat023 block000_data_flat024) := by decide +kernel
theorem block000_data_flat025_original : block000_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)) := by
  rw [block000_data_flat025_step, block000_data_flat023_original, block000_data_flat024_original]
def block000_data_flat026 : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380))]
theorem block000_data_flat026_step : block000_data_flat026 = (CoefficientMerge.fastMerge block000_data_flat022 block000_data_flat025) := by decide +kernel
theorem block000_data_flat026_original : block000_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded))) := by
  rw [block000_data_flat026_step, block000_data_flat022_original, block000_data_flat025_original]
def block000_data_flat027 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380))]
theorem block000_data_flat027_step : block000_data_flat027 = (CoefficientMerge.fastMerge block000_data_flat021 block000_data_flat026) := by decide +kernel
theorem block000_data_flat027_original : block000_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) := by
  rw [block000_data_flat027_step, block000_data_flat021_original, block000_data_flat026_original]
def block000_data_flat028 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 158040))]
theorem block000_data_flat028_step : block000_data_flat028 = (CoefficientMerge.scale (158040 : Int) atom0015Coded) := by decide +kernel
theorem block000_data_flat028_original : block000_data_flat028 = (CoefficientMerge.scale (158040 : Int) atom0015Coded) := by
  rw [block000_data_flat028_step]
def block000_data_flat029 : CoefficientMerge.Poly := [(nat_lit 25, Int.ofNat (nat_lit 139500))]
theorem block000_data_flat029_step : block000_data_flat029 = (CoefficientMerge.scale (139500 : Int) atom0016Coded) := by decide +kernel
theorem block000_data_flat029_original : block000_data_flat029 = (CoefficientMerge.scale (139500 : Int) atom0016Coded) := by
  rw [block000_data_flat029_step]
def block000_data_flat030 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500))]
theorem block000_data_flat030_step : block000_data_flat030 = (CoefficientMerge.fastMerge block000_data_flat028 block000_data_flat029) := by decide +kernel
theorem block000_data_flat030_original : block000_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) := by
  rw [block000_data_flat030_step, block000_data_flat028_original, block000_data_flat029_original]
def block000_data_flat031 : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 34200))]
theorem block000_data_flat031_step : block000_data_flat031 = (CoefficientMerge.scale (34200 : Int) atom0017Coded) := by decide +kernel
theorem block000_data_flat031_original : block000_data_flat031 = (CoefficientMerge.scale (34200 : Int) atom0017Coded) := by
  rw [block000_data_flat031_step]
def block000_data_flat032 : CoefficientMerge.Poly := [(nat_lit 30, Int.ofNat (nat_lit 508320))]
theorem block000_data_flat032_step : block000_data_flat032 = (CoefficientMerge.scale (508320 : Int) atom0018Coded) := by decide +kernel
theorem block000_data_flat032_original : block000_data_flat032 = (CoefficientMerge.scale (508320 : Int) atom0018Coded) := by
  rw [block000_data_flat032_step]
def block000_data_flat033 : CoefficientMerge.Poly := [(nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat033_step : block000_data_flat033 = (CoefficientMerge.scale (843120 : Int) atom0019Coded) := by decide +kernel
theorem block000_data_flat033_original : block000_data_flat033 = (CoefficientMerge.scale (843120 : Int) atom0019Coded) := by
  rw [block000_data_flat033_step]
def block000_data_flat034 : CoefficientMerge.Poly := [(nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat034_step : block000_data_flat034 = (CoefficientMerge.fastMerge block000_data_flat032 block000_data_flat033) := by decide +kernel
theorem block000_data_flat034_original : block000_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)) := by
  rw [block000_data_flat034_step, block000_data_flat032_original, block000_data_flat033_original]
def block000_data_flat035 : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat035_step : block000_data_flat035 = (CoefficientMerge.fastMerge block000_data_flat031 block000_data_flat034) := by decide +kernel
theorem block000_data_flat035_original : block000_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded))) := by
  rw [block000_data_flat035_step, block000_data_flat031_original, block000_data_flat034_original]
def block000_data_flat036 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat036_step : block000_data_flat036 = (CoefficientMerge.fastMerge block000_data_flat030 block000_data_flat035) := by decide +kernel
theorem block000_data_flat036_original : block000_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))) := by
  rw [block000_data_flat036_step, block000_data_flat030_original, block000_data_flat035_original]
def block000_data_flat037 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat037_step : block000_data_flat037 = (CoefficientMerge.fastMerge block000_data_flat027 block000_data_flat036) := by decide +kernel
theorem block000_data_flat037_original : block000_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded))))) := by
  rw [block000_data_flat037_step, block000_data_flat027_original, block000_data_flat036_original]
def block000_data_flat038 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540)), (nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120))]
theorem block000_data_flat038_step : block000_data_flat038 = (CoefficientMerge.fastMerge block000_data_flat018 block000_data_flat037) := by decide +kernel
theorem block000_data_flat038_original : block000_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) := by
  rw [block000_data_flat038_step, block000_data_flat018_original, block000_data_flat037_original]
def block000_data_flat039 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 804060))]
theorem block000_data_flat039_step : block000_data_flat039 = (CoefficientMerge.scale (804060 : Int) atom0020Coded) := by decide +kernel
theorem block000_data_flat039_original : block000_data_flat039 = (CoefficientMerge.scale (804060 : Int) atom0020Coded) := by
  rw [block000_data_flat039_step]
def block000_data_flat040 : CoefficientMerge.Poly := [(nat_lit 33, Int.ofNat (nat_lit 729360))]
theorem block000_data_flat040_step : block000_data_flat040 = (CoefficientMerge.scale (729360 : Int) atom0021Coded) := by decide +kernel
theorem block000_data_flat040_original : block000_data_flat040 = (CoefficientMerge.scale (729360 : Int) atom0021Coded) := by
  rw [block000_data_flat040_step]
def block000_data_flat041 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360))]
theorem block000_data_flat041_step : block000_data_flat041 = (CoefficientMerge.fastMerge block000_data_flat039 block000_data_flat040) := by decide +kernel
theorem block000_data_flat041_original : block000_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) := by
  rw [block000_data_flat041_step, block000_data_flat039_original, block000_data_flat040_original]
def block000_data_flat042 : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 344700))]
theorem block000_data_flat042_step : block000_data_flat042 = (CoefficientMerge.scale (344700 : Int) atom0022Coded) := by decide +kernel
theorem block000_data_flat042_original : block000_data_flat042 = (CoefficientMerge.scale (344700 : Int) atom0022Coded) := by
  rw [block000_data_flat042_step]
def block000_data_flat043 : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 388080))]
theorem block000_data_flat043_step : block000_data_flat043 = (CoefficientMerge.scale (388080 : Int) atom0023Coded) := by decide +kernel
theorem block000_data_flat043_original : block000_data_flat043 = (CoefficientMerge.scale (388080 : Int) atom0023Coded) := by
  rw [block000_data_flat043_step]
def block000_data_flat044 : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 382464))]
theorem block000_data_flat044_step : block000_data_flat044 = (CoefficientMerge.scale (382464 : Int) atom0024Coded) := by decide +kernel
theorem block000_data_flat044_original : block000_data_flat044 = (CoefficientMerge.scale (382464 : Int) atom0024Coded) := by
  rw [block000_data_flat044_step]
def block000_data_flat045 : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464))]
theorem block000_data_flat045_step : block000_data_flat045 = (CoefficientMerge.fastMerge block000_data_flat043 block000_data_flat044) := by decide +kernel
theorem block000_data_flat045_original : block000_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)) := by
  rw [block000_data_flat045_step, block000_data_flat043_original, block000_data_flat044_original]
def block000_data_flat046 : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464))]
theorem block000_data_flat046_step : block000_data_flat046 = (CoefficientMerge.fastMerge block000_data_flat042 block000_data_flat045) := by decide +kernel
theorem block000_data_flat046_original : block000_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded))) := by
  rw [block000_data_flat046_step, block000_data_flat042_original, block000_data_flat045_original]
def block000_data_flat047 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464))]
theorem block000_data_flat047_step : block000_data_flat047 = (CoefficientMerge.fastMerge block000_data_flat041 block000_data_flat046) := by decide +kernel
theorem block000_data_flat047_original : block000_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) := by
  rw [block000_data_flat047_step, block000_data_flat041_original, block000_data_flat046_original]
def block000_data_flat048 : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 715680))]
theorem block000_data_flat048_step : block000_data_flat048 = (CoefficientMerge.scale (715680 : Int) atom0025Coded) := by decide +kernel
theorem block000_data_flat048_original : block000_data_flat048 = (CoefficientMerge.scale (715680 : Int) atom0025Coded) := by
  rw [block000_data_flat048_step]
def block000_data_flat049 : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 812160))]
theorem block000_data_flat049_step : block000_data_flat049 = (CoefficientMerge.scale (812160 : Int) atom0026Coded) := by decide +kernel
theorem block000_data_flat049_original : block000_data_flat049 = (CoefficientMerge.scale (812160 : Int) atom0026Coded) := by
  rw [block000_data_flat049_step]
def block000_data_flat050 : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160))]
theorem block000_data_flat050_step : block000_data_flat050 = (CoefficientMerge.fastMerge block000_data_flat048 block000_data_flat049) := by decide +kernel
theorem block000_data_flat050_original : block000_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) := by
  rw [block000_data_flat050_step, block000_data_flat048_original, block000_data_flat049_original]
def block000_data_flat051 : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 436500))]
theorem block000_data_flat051_step : block000_data_flat051 = (CoefficientMerge.scale (436500 : Int) atom0027Coded) := by decide +kernel
theorem block000_data_flat051_original : block000_data_flat051 = (CoefficientMerge.scale (436500 : Int) atom0027Coded) := by
  rw [block000_data_flat051_step]
def block000_data_flat052 : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 544320))]
theorem block000_data_flat052_step : block000_data_flat052 = (CoefficientMerge.scale (544320 : Int) atom0028Coded) := by decide +kernel
theorem block000_data_flat052_original : block000_data_flat052 = (CoefficientMerge.scale (544320 : Int) atom0028Coded) := by
  rw [block000_data_flat052_step]
def block000_data_flat053 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 380880))]
theorem block000_data_flat053_step : block000_data_flat053 = (CoefficientMerge.scale (380880 : Int) atom0029Coded) := by decide +kernel
theorem block000_data_flat053_original : block000_data_flat053 = (CoefficientMerge.scale (380880 : Int) atom0029Coded) := by
  rw [block000_data_flat053_step]
def block000_data_flat054 : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880))]
theorem block000_data_flat054_step : block000_data_flat054 = (CoefficientMerge.fastMerge block000_data_flat052 block000_data_flat053) := by decide +kernel
theorem block000_data_flat054_original : block000_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded)) := by
  rw [block000_data_flat054_step, block000_data_flat052_original, block000_data_flat053_original]
def block000_data_flat055 : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880))]
theorem block000_data_flat055_step : block000_data_flat055 = (CoefficientMerge.fastMerge block000_data_flat051 block000_data_flat054) := by decide +kernel
theorem block000_data_flat055_original : block000_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))) := by
  rw [block000_data_flat055_step, block000_data_flat051_original, block000_data_flat054_original]
def block000_data_flat056 : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880))]
theorem block000_data_flat056_step : block000_data_flat056 = (CoefficientMerge.fastMerge block000_data_flat050 block000_data_flat055) := by decide +kernel
theorem block000_data_flat056_original : block000_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded)))) := by
  rw [block000_data_flat056_step, block000_data_flat050_original, block000_data_flat055_original]
def block000_data_flat057 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880))]
theorem block000_data_flat057_step : block000_data_flat057 = (CoefficientMerge.fastMerge block000_data_flat047 block000_data_flat056) := by decide +kernel
theorem block000_data_flat057_original : block000_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) := by
  rw [block000_data_flat057_step, block000_data_flat047_original, block000_data_flat056_original]
def block000_data_flat058 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 894960))]
theorem block000_data_flat058_step : block000_data_flat058 = (CoefficientMerge.scale (894960 : Int) atom0030Coded) := by decide +kernel
theorem block000_data_flat058_original : block000_data_flat058 = (CoefficientMerge.scale (894960 : Int) atom0030Coded) := by
  rw [block000_data_flat058_step]
def block000_data_flat059 : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 500580))]
theorem block000_data_flat059_step : block000_data_flat059 = (CoefficientMerge.scale (500580 : Int) atom0031Coded) := by decide +kernel
theorem block000_data_flat059_original : block000_data_flat059 = (CoefficientMerge.scale (500580 : Int) atom0031Coded) := by
  rw [block000_data_flat059_step]
def block000_data_flat060 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580))]
theorem block000_data_flat060_step : block000_data_flat060 = (CoefficientMerge.fastMerge block000_data_flat058 block000_data_flat059) := by decide +kernel
theorem block000_data_flat060_original : block000_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) := by
  rw [block000_data_flat060_step, block000_data_flat058_original, block000_data_flat059_original]
def block000_data_flat061 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 470160))]
theorem block000_data_flat061_step : block000_data_flat061 = (CoefficientMerge.scale (470160 : Int) atom0032Coded) := by decide +kernel
theorem block000_data_flat061_original : block000_data_flat061 = (CoefficientMerge.scale (470160 : Int) atom0032Coded) := by
  rw [block000_data_flat061_step]
def block000_data_flat062 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 488880))]
theorem block000_data_flat062_step : block000_data_flat062 = (CoefficientMerge.scale (488880 : Int) atom0033Coded) := by decide +kernel
theorem block000_data_flat062_original : block000_data_flat062 = (CoefficientMerge.scale (488880 : Int) atom0033Coded) := by
  rw [block000_data_flat062_step]
def block000_data_flat063 : CoefficientMerge.Poly := [(nat_lit 61, Int.ofNat (nat_lit 592380))]
theorem block000_data_flat063_step : block000_data_flat063 = (CoefficientMerge.scale (592380 : Int) atom0034Coded) := by decide +kernel
theorem block000_data_flat063_original : block000_data_flat063 = (CoefficientMerge.scale (592380 : Int) atom0034Coded) := by
  rw [block000_data_flat063_step]
def block000_data_flat064 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380))]
theorem block000_data_flat064_step : block000_data_flat064 = (CoefficientMerge.fastMerge block000_data_flat062 block000_data_flat063) := by decide +kernel
theorem block000_data_flat064_original : block000_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)) := by
  rw [block000_data_flat064_step, block000_data_flat062_original, block000_data_flat063_original]
def block000_data_flat065 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380))]
theorem block000_data_flat065_step : block000_data_flat065 = (CoefficientMerge.fastMerge block000_data_flat061 block000_data_flat064) := by decide +kernel
theorem block000_data_flat065_original : block000_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded))) := by
  rw [block000_data_flat065_step, block000_data_flat061_original, block000_data_flat064_original]
def block000_data_flat066 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380))]
theorem block000_data_flat066_step : block000_data_flat066 = (CoefficientMerge.fastMerge block000_data_flat060 block000_data_flat065) := by decide +kernel
theorem block000_data_flat066_original : block000_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) := by
  rw [block000_data_flat066_step, block000_data_flat060_original, block000_data_flat065_original]
def block000_data_flat067 : CoefficientMerge.Poly := [(nat_lit 62, Int.ofNat (nat_lit 626400))]
theorem block000_data_flat067_step : block000_data_flat067 = (CoefficientMerge.scale (626400 : Int) atom0035Coded) := by decide +kernel
theorem block000_data_flat067_original : block000_data_flat067 = (CoefficientMerge.scale (626400 : Int) atom0035Coded) := by
  rw [block000_data_flat067_step]
def block000_data_flat068 : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 60300))]
theorem block000_data_flat068_step : block000_data_flat068 = (CoefficientMerge.scale (60300 : Int) atom0036Coded) := by decide +kernel
theorem block000_data_flat068_original : block000_data_flat068 = (CoefficientMerge.scale (60300 : Int) atom0036Coded) := by
  rw [block000_data_flat068_step]
def block000_data_flat069 : CoefficientMerge.Poly := [(nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300))]
theorem block000_data_flat069_step : block000_data_flat069 = (CoefficientMerge.fastMerge block000_data_flat067 block000_data_flat068) := by decide +kernel
theorem block000_data_flat069_original : block000_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) := by
  rw [block000_data_flat069_step, block000_data_flat067_original, block000_data_flat068_original]
def block000_data_flat070 : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 110700))]
theorem block000_data_flat070_step : block000_data_flat070 = (CoefficientMerge.scale (110700 : Int) atom0037Coded) := by decide +kernel
theorem block000_data_flat070_original : block000_data_flat070 = (CoefficientMerge.scale (110700 : Int) atom0037Coded) := by
  rw [block000_data_flat070_step]
def block000_data_flat071 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 360))]
theorem block000_data_flat071_step : block000_data_flat071 = (CoefficientMerge.scale (360 : Int) atom0038Coded) := by decide +kernel
theorem block000_data_flat071_original : block000_data_flat071 = (CoefficientMerge.scale (360 : Int) atom0038Coded) := by
  rw [block000_data_flat071_step]
def block000_data_flat072 : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat072_step : block000_data_flat072 = (CoefficientMerge.scale (11280 : Int) atom0039Coded) := by decide +kernel
theorem block000_data_flat072_original : block000_data_flat072 = (CoefficientMerge.scale (11280 : Int) atom0039Coded) := by
  rw [block000_data_flat072_step]
def block000_data_flat073 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat073_step : block000_data_flat073 = (CoefficientMerge.fastMerge block000_data_flat071 block000_data_flat072) := by decide +kernel
theorem block000_data_flat073_original : block000_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded)) := by
  rw [block000_data_flat073_step, block000_data_flat071_original, block000_data_flat072_original]
def block000_data_flat074 : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat074_step : block000_data_flat074 = (CoefficientMerge.fastMerge block000_data_flat070 block000_data_flat073) := by decide +kernel
theorem block000_data_flat074_original : block000_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))) := by
  rw [block000_data_flat074_step, block000_data_flat070_original, block000_data_flat073_original]
def block000_data_flat075 : CoefficientMerge.Poly := [(nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat075_step : block000_data_flat075 = (CoefficientMerge.fastMerge block000_data_flat069 block000_data_flat074) := by decide +kernel
theorem block000_data_flat075_original : block000_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded)))) := by
  rw [block000_data_flat075_step, block000_data_flat069_original, block000_data_flat074_original]
def block000_data_flat076 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat076_step : block000_data_flat076 = (CoefficientMerge.fastMerge block000_data_flat066 block000_data_flat075) := by decide +kernel
theorem block000_data_flat076_original : block000_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))) := by
  rw [block000_data_flat076_step, block000_data_flat066_original, block000_data_flat075_original]
def block000_data_flat077 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880)), (nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat077_step : block000_data_flat077 = (CoefficientMerge.fastMerge block000_data_flat057 block000_data_flat076) := by decide +kernel
theorem block000_data_flat077_original : block000_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded)))))) := by
  rw [block000_data_flat077_step, block000_data_flat057_original, block000_data_flat076_original]
def block000_data_flat078 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540)), (nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120)), (nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880)), (nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280))]
theorem block000_data_flat078_step : block000_data_flat078 = (CoefficientMerge.fastMerge block000_data_flat038 block000_data_flat077) := by decide +kernel
theorem block000_data_flat078_original : block000_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))))) := by
  rw [block000_data_flat078_step, block000_data_flat038_original, block000_data_flat077_original]
def block000_data_flat079 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940))]
theorem block000_data_flat079_step : block000_data_flat079 = (CoefficientMerge.scale (209940 : Int) atom0040Coded) := by decide +kernel
theorem block000_data_flat079_original : block000_data_flat079 = (CoefficientMerge.scale (209940 : Int) atom0040Coded) := by
  rw [block000_data_flat079_step]
def block000_data_flat080 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 1380))]
theorem block000_data_flat080_step : block000_data_flat080 = (CoefficientMerge.scale (1380 : Int) atom0041Coded) := by decide +kernel
theorem block000_data_flat080_original : block000_data_flat080 = (CoefficientMerge.scale (1380 : Int) atom0041Coded) := by
  rw [block000_data_flat080_step]
def block000_data_flat081 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380))]
theorem block000_data_flat081_step : block000_data_flat081 = (CoefficientMerge.fastMerge block000_data_flat079 block000_data_flat080) := by decide +kernel
theorem block000_data_flat081_original : block000_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) := by
  rw [block000_data_flat081_step, block000_data_flat079_original, block000_data_flat080_original]
def block000_data_flat082 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 12960))]
theorem block000_data_flat082_step : block000_data_flat082 = (CoefficientMerge.scale (12960 : Int) atom0042Coded) := by decide +kernel
theorem block000_data_flat082_original : block000_data_flat082 = (CoefficientMerge.scale (12960 : Int) atom0042Coded) := by
  rw [block000_data_flat082_step]
def block000_data_flat083 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 538560))]
theorem block000_data_flat083_step : block000_data_flat083 = (CoefficientMerge.scale (538560 : Int) atom0043Coded) := by decide +kernel
theorem block000_data_flat083_original : block000_data_flat083 = (CoefficientMerge.scale (538560 : Int) atom0043Coded) := by
  rw [block000_data_flat083_step]
def block000_data_flat084 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 223280))]
theorem block000_data_flat084_step : block000_data_flat084 = (CoefficientMerge.scale (223280 : Int) atom0044Coded) := by decide +kernel
theorem block000_data_flat084_original : block000_data_flat084 = (CoefficientMerge.scale (223280 : Int) atom0044Coded) := by
  rw [block000_data_flat084_step]
def block000_data_flat085 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280))]
theorem block000_data_flat085_step : block000_data_flat085 = (CoefficientMerge.fastMerge block000_data_flat083 block000_data_flat084) := by decide +kernel
theorem block000_data_flat085_original : block000_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)) := by
  rw [block000_data_flat085_step, block000_data_flat083_original, block000_data_flat084_original]
def block000_data_flat086 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280))]
theorem block000_data_flat086_step : block000_data_flat086 = (CoefficientMerge.fastMerge block000_data_flat082 block000_data_flat085) := by decide +kernel
theorem block000_data_flat086_original : block000_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded))) := by
  rw [block000_data_flat086_step, block000_data_flat082_original, block000_data_flat085_original]
def block000_data_flat087 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280))]
theorem block000_data_flat087_step : block000_data_flat087 = (CoefficientMerge.fastMerge block000_data_flat081 block000_data_flat086) := by decide +kernel
theorem block000_data_flat087_original : block000_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) := by
  rw [block000_data_flat087_step, block000_data_flat081_original, block000_data_flat086_original]
def block000_data_flat088 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 334260))]
theorem block000_data_flat088_step : block000_data_flat088 = (CoefficientMerge.scale (334260 : Int) atom0045Coded) := by decide +kernel
theorem block000_data_flat088_original : block000_data_flat088 = (CoefficientMerge.scale (334260 : Int) atom0045Coded) := by
  rw [block000_data_flat088_step]
def block000_data_flat089 : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 443520))]
theorem block000_data_flat089_step : block000_data_flat089 = (CoefficientMerge.scale (443520 : Int) atom0046Coded) := by decide +kernel
theorem block000_data_flat089_original : block000_data_flat089 = (CoefficientMerge.scale (443520 : Int) atom0046Coded) := by
  rw [block000_data_flat089_step]
def block000_data_flat090 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520))]
theorem block000_data_flat090_step : block000_data_flat090 = (CoefficientMerge.fastMerge block000_data_flat088 block000_data_flat089) := by decide +kernel
theorem block000_data_flat090_original : block000_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) := by
  rw [block000_data_flat090_step, block000_data_flat088_original, block000_data_flat089_original]
def block000_data_flat091 : CoefficientMerge.Poly := [(nat_lit 106, Int.ofNat (nat_lit 404920))]
theorem block000_data_flat091_step : block000_data_flat091 = (CoefficientMerge.scale (404920 : Int) atom0047Coded) := by decide +kernel
theorem block000_data_flat091_original : block000_data_flat091 = (CoefficientMerge.scale (404920 : Int) atom0047Coded) := by
  rw [block000_data_flat091_step]
def block000_data_flat092 : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 560400))]
theorem block000_data_flat092_step : block000_data_flat092 = (CoefficientMerge.scale (560400 : Int) atom0048Coded) := by decide +kernel
theorem block000_data_flat092_original : block000_data_flat092 = (CoefficientMerge.scale (560400 : Int) atom0048Coded) := by
  rw [block000_data_flat092_step]
def block000_data_flat093 : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 475200))]
theorem block000_data_flat093_step : block000_data_flat093 = (CoefficientMerge.scale (475200 : Int) atom0049Coded) := by decide +kernel
theorem block000_data_flat093_original : block000_data_flat093 = (CoefficientMerge.scale (475200 : Int) atom0049Coded) := by
  rw [block000_data_flat093_step]
def block000_data_flat094 : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200))]
theorem block000_data_flat094_step : block000_data_flat094 = (CoefficientMerge.fastMerge block000_data_flat092 block000_data_flat093) := by decide +kernel
theorem block000_data_flat094_original : block000_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded)) := by
  rw [block000_data_flat094_step, block000_data_flat092_original, block000_data_flat093_original]
def block000_data_flat095 : CoefficientMerge.Poly := [(nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200))]
theorem block000_data_flat095_step : block000_data_flat095 = (CoefficientMerge.fastMerge block000_data_flat091 block000_data_flat094) := by decide +kernel
theorem block000_data_flat095_original : block000_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))) := by
  rw [block000_data_flat095_step, block000_data_flat091_original, block000_data_flat094_original]
def block000_data_flat096 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200))]
theorem block000_data_flat096_step : block000_data_flat096 = (CoefficientMerge.fastMerge block000_data_flat090 block000_data_flat095) := by decide +kernel
theorem block000_data_flat096_original : block000_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded)))) := by
  rw [block000_data_flat096_step, block000_data_flat090_original, block000_data_flat095_original]
def block000_data_flat097 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200))]
theorem block000_data_flat097_step : block000_data_flat097 = (CoefficientMerge.fastMerge block000_data_flat087 block000_data_flat096) := by decide +kernel
theorem block000_data_flat097_original : block000_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) := by
  rw [block000_data_flat097_step, block000_data_flat087_original, block000_data_flat096_original]
def block000_data_flat098 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 655960))]
theorem block000_data_flat098_step : block000_data_flat098 = (CoefficientMerge.scale (655960 : Int) atom0050Coded) := by decide +kernel
theorem block000_data_flat098_original : block000_data_flat098 = (CoefficientMerge.scale (655960 : Int) atom0050Coded) := by
  rw [block000_data_flat098_step]
def block000_data_flat099 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 892980))]
theorem block000_data_flat099_step : block000_data_flat099 = (CoefficientMerge.scale (892980 : Int) atom0051Coded) := by decide +kernel
theorem block000_data_flat099_original : block000_data_flat099 = (CoefficientMerge.scale (892980 : Int) atom0051Coded) := by
  rw [block000_data_flat099_step]
def block000_data_flat100 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980))]
theorem block000_data_flat100_step : block000_data_flat100 = (CoefficientMerge.fastMerge block000_data_flat098 block000_data_flat099) := by decide +kernel
theorem block000_data_flat100_original : block000_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) := by
  rw [block000_data_flat100_step, block000_data_flat098_original, block000_data_flat099_original]
def block000_data_flat101 : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1075680))]
theorem block000_data_flat101_step : block000_data_flat101 = (CoefficientMerge.scale (1075680 : Int) atom0052Coded) := by decide +kernel
theorem block000_data_flat101_original : block000_data_flat101 = (CoefficientMerge.scale (1075680 : Int) atom0052Coded) := by
  rw [block000_data_flat101_step]
def block000_data_flat102 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 559400))]
theorem block000_data_flat102_step : block000_data_flat102 = (CoefficientMerge.scale (559400 : Int) atom0053Coded) := by decide +kernel
theorem block000_data_flat102_original : block000_data_flat102 = (CoefficientMerge.scale (559400 : Int) atom0053Coded) := by
  rw [block000_data_flat102_step]
def block000_data_flat103 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 745140))]
theorem block000_data_flat103_step : block000_data_flat103 = (CoefficientMerge.scale (745140 : Int) atom0054Coded) := by decide +kernel
theorem block000_data_flat103_original : block000_data_flat103 = (CoefficientMerge.scale (745140 : Int) atom0054Coded) := by
  rw [block000_data_flat103_step]
def block000_data_flat104 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140))]
theorem block000_data_flat104_step : block000_data_flat104 = (CoefficientMerge.fastMerge block000_data_flat102 block000_data_flat103) := by decide +kernel
theorem block000_data_flat104_original : block000_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)) := by
  rw [block000_data_flat104_step, block000_data_flat102_original, block000_data_flat103_original]
def block000_data_flat105 : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140))]
theorem block000_data_flat105_step : block000_data_flat105 = (CoefficientMerge.fastMerge block000_data_flat101 block000_data_flat104) := by decide +kernel
theorem block000_data_flat105_original : block000_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded))) := by
  rw [block000_data_flat105_step, block000_data_flat101_original, block000_data_flat104_original]
def block000_data_flat106 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140))]
theorem block000_data_flat106_step : block000_data_flat106 = (CoefficientMerge.fastMerge block000_data_flat100 block000_data_flat105) := by decide +kernel
theorem block000_data_flat106_original : block000_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) := by
  rw [block000_data_flat106_step, block000_data_flat100_original, block000_data_flat105_original]
def block000_data_flat107 : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 213356))]
theorem block000_data_flat107_step : block000_data_flat107 = (CoefficientMerge.scale (213356 : Int) atom0055Coded) := by decide +kernel
theorem block000_data_flat107_original : block000_data_flat107 = (CoefficientMerge.scale (213356 : Int) atom0055Coded) := by
  rw [block000_data_flat107_step]
def block000_data_flat108 : CoefficientMerge.Poly := [(nat_lit 122, Int.ofNat (nat_lit 591100))]
theorem block000_data_flat108_step : block000_data_flat108 = (CoefficientMerge.scale (591100 : Int) atom0056Coded) := by decide +kernel
theorem block000_data_flat108_original : block000_data_flat108 = (CoefficientMerge.scale (591100 : Int) atom0056Coded) := by
  rw [block000_data_flat108_step]
def block000_data_flat109 : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100))]
theorem block000_data_flat109_step : block000_data_flat109 = (CoefficientMerge.fastMerge block000_data_flat107 block000_data_flat108) := by decide +kernel
theorem block000_data_flat109_original : block000_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) := by
  rw [block000_data_flat109_step, block000_data_flat107_original, block000_data_flat108_original]
def block000_data_flat110 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 968550))]
theorem block000_data_flat110_step : block000_data_flat110 = (CoefficientMerge.scale (968550 : Int) atom0057Coded) := by decide +kernel
theorem block000_data_flat110_original : block000_data_flat110 = (CoefficientMerge.scale (968550 : Int) atom0057Coded) := by
  rw [block000_data_flat110_step]
def block000_data_flat111 : CoefficientMerge.Poly := [(nat_lit 124, Int.ofNat (nat_lit 700670))]
theorem block000_data_flat111_step : block000_data_flat111 = (CoefficientMerge.scale (700670 : Int) atom0058Coded) := by decide +kernel
theorem block000_data_flat111_original : block000_data_flat111 = (CoefficientMerge.scale (700670 : Int) atom0058Coded) := by
  rw [block000_data_flat111_step]
def block000_data_flat112 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat112_step : block000_data_flat112 = (CoefficientMerge.scale (874770 : Int) atom0059Coded) := by decide +kernel
theorem block000_data_flat112_original : block000_data_flat112 = (CoefficientMerge.scale (874770 : Int) atom0059Coded) := by
  rw [block000_data_flat112_step]
def block000_data_flat113 : CoefficientMerge.Poly := [(nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat113_step : block000_data_flat113 = (CoefficientMerge.fastMerge block000_data_flat111 block000_data_flat112) := by decide +kernel
theorem block000_data_flat113_original : block000_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)) := by
  rw [block000_data_flat113_step, block000_data_flat111_original, block000_data_flat112_original]
def block000_data_flat114 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat114_step : block000_data_flat114 = (CoefficientMerge.fastMerge block000_data_flat110 block000_data_flat113) := by decide +kernel
theorem block000_data_flat114_original : block000_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded))) := by
  rw [block000_data_flat114_step, block000_data_flat110_original, block000_data_flat113_original]
def block000_data_flat115 : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat115_step : block000_data_flat115 = (CoefficientMerge.fastMerge block000_data_flat109 block000_data_flat114) := by decide +kernel
theorem block000_data_flat115_original : block000_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))) := by
  rw [block000_data_flat115_step, block000_data_flat109_original, block000_data_flat114_original]
def block000_data_flat116 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat116_step : block000_data_flat116 = (CoefficientMerge.fastMerge block000_data_flat106 block000_data_flat115) := by decide +kernel
theorem block000_data_flat116_original : block000_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded))))) := by
  rw [block000_data_flat116_step, block000_data_flat106_original, block000_data_flat115_original]
def block000_data_flat117 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200)), (nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770))]
theorem block000_data_flat117_step : block000_data_flat117 = (CoefficientMerge.fastMerge block000_data_flat097 block000_data_flat116) := by decide +kernel
theorem block000_data_flat117_original : block000_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) := by
  rw [block000_data_flat117_step, block000_data_flat097_original, block000_data_flat116_original]
def block000_data_flat118 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 489240))]
theorem block000_data_flat118_step : block000_data_flat118 = (CoefficientMerge.scale (489240 : Int) atom0060Coded) := by decide +kernel
theorem block000_data_flat118_original : block000_data_flat118 = (CoefficientMerge.scale (489240 : Int) atom0060Coded) := by
  rw [block000_data_flat118_step]
def block000_data_flat119 : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 975960))]
theorem block000_data_flat119_step : block000_data_flat119 = (CoefficientMerge.scale (975960 : Int) atom0061Coded) := by decide +kernel
theorem block000_data_flat119_original : block000_data_flat119 = (CoefficientMerge.scale (975960 : Int) atom0061Coded) := by
  rw [block000_data_flat119_step]
def block000_data_flat120 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960))]
theorem block000_data_flat120_step : block000_data_flat120 = (CoefficientMerge.fastMerge block000_data_flat118 block000_data_flat119) := by decide +kernel
theorem block000_data_flat120_original : block000_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) := by
  rw [block000_data_flat120_step, block000_data_flat118_original, block000_data_flat119_original]
def block000_data_flat121 : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 743780))]
theorem block000_data_flat121_step : block000_data_flat121 = (CoefficientMerge.scale (743780 : Int) atom0062Coded) := by decide +kernel
theorem block000_data_flat121_original : block000_data_flat121 = (CoefficientMerge.scale (743780 : Int) atom0062Coded) := by
  rw [block000_data_flat121_step]
def block000_data_flat122 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 978960))]
theorem block000_data_flat122_step : block000_data_flat122 = (CoefficientMerge.scale (978960 : Int) atom0063Coded) := by decide +kernel
theorem block000_data_flat122_original : block000_data_flat122 = (CoefficientMerge.scale (978960 : Int) atom0063Coded) := by
  rw [block000_data_flat122_step]
def block000_data_flat123 : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 436320))]
theorem block000_data_flat123_step : block000_data_flat123 = (CoefficientMerge.scale (436320 : Int) atom0064Coded) := by decide +kernel
theorem block000_data_flat123_original : block000_data_flat123 = (CoefficientMerge.scale (436320 : Int) atom0064Coded) := by
  rw [block000_data_flat123_step]
def block000_data_flat124 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320))]
theorem block000_data_flat124_step : block000_data_flat124 = (CoefficientMerge.fastMerge block000_data_flat122 block000_data_flat123) := by decide +kernel
theorem block000_data_flat124_original : block000_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)) := by
  rw [block000_data_flat124_step, block000_data_flat122_original, block000_data_flat123_original]
def block000_data_flat125 : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320))]
theorem block000_data_flat125_step : block000_data_flat125 = (CoefficientMerge.fastMerge block000_data_flat121 block000_data_flat124) := by decide +kernel
theorem block000_data_flat125_original : block000_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded))) := by
  rw [block000_data_flat125_step, block000_data_flat121_original, block000_data_flat124_original]
def block000_data_flat126 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320))]
theorem block000_data_flat126_step : block000_data_flat126 = (CoefficientMerge.fastMerge block000_data_flat120 block000_data_flat125) := by decide +kernel
theorem block000_data_flat126_original : block000_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) := by
  rw [block000_data_flat126_step, block000_data_flat120_original, block000_data_flat125_original]
def block000_data_flat127 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 697890))]
theorem block000_data_flat127_step : block000_data_flat127 = (CoefficientMerge.scale (697890 : Int) atom0065Coded) := by decide +kernel
theorem block000_data_flat127_original : block000_data_flat127 = (CoefficientMerge.scale (697890 : Int) atom0065Coded) := by
  rw [block000_data_flat127_step]
def block000_data_flat128 : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 989850))]
theorem block000_data_flat128_step : block000_data_flat128 = (CoefficientMerge.scale (989850 : Int) atom0066Coded) := by decide +kernel
theorem block000_data_flat128_original : block000_data_flat128 = (CoefficientMerge.scale (989850 : Int) atom0066Coded) := by
  rw [block000_data_flat128_step]
def block000_data_flat129 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850))]
theorem block000_data_flat129_step : block000_data_flat129 = (CoefficientMerge.fastMerge block000_data_flat127 block000_data_flat128) := by decide +kernel
theorem block000_data_flat129_original : block000_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) := by
  rw [block000_data_flat129_step, block000_data_flat127_original, block000_data_flat128_original]
def block000_data_flat130 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 179150))]
theorem block000_data_flat130_step : block000_data_flat130 = (CoefficientMerge.scale (179150 : Int) atom0067Coded) := by decide +kernel
theorem block000_data_flat130_original : block000_data_flat130 = (CoefficientMerge.scale (179150 : Int) atom0067Coded) := by
  rw [block000_data_flat130_step]
def block000_data_flat131 : CoefficientMerge.Poly := [(nat_lit 152, Int.ofNat (nat_lit 626340))]
theorem block000_data_flat131_step : block000_data_flat131 = (CoefficientMerge.scale (626340 : Int) atom0068Coded) := by decide +kernel
theorem block000_data_flat131_original : block000_data_flat131 = (CoefficientMerge.scale (626340 : Int) atom0068Coded) := by
  rw [block000_data_flat131_step]
def block000_data_flat132 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 331830))]
theorem block000_data_flat132_step : block000_data_flat132 = (CoefficientMerge.scale (331830 : Int) atom0069Coded) := by decide +kernel
theorem block000_data_flat132_original : block000_data_flat132 = (CoefficientMerge.scale (331830 : Int) atom0069Coded) := by
  rw [block000_data_flat132_step]
def block000_data_flat133 : CoefficientMerge.Poly := [(nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830))]
theorem block000_data_flat133_step : block000_data_flat133 = (CoefficientMerge.fastMerge block000_data_flat131 block000_data_flat132) := by decide +kernel
theorem block000_data_flat133_original : block000_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded)) := by
  rw [block000_data_flat133_step, block000_data_flat131_original, block000_data_flat132_original]
def block000_data_flat134 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830))]
theorem block000_data_flat134_step : block000_data_flat134 = (CoefficientMerge.fastMerge block000_data_flat130 block000_data_flat133) := by decide +kernel
theorem block000_data_flat134_original : block000_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))) := by
  rw [block000_data_flat134_step, block000_data_flat130_original, block000_data_flat133_original]
def block000_data_flat135 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830))]
theorem block000_data_flat135_step : block000_data_flat135 = (CoefficientMerge.fastMerge block000_data_flat129 block000_data_flat134) := by decide +kernel
theorem block000_data_flat135_original : block000_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded)))) := by
  rw [block000_data_flat135_step, block000_data_flat129_original, block000_data_flat134_original]
def block000_data_flat136 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830))]
theorem block000_data_flat136_step : block000_data_flat136 = (CoefficientMerge.fastMerge block000_data_flat126 block000_data_flat135) := by decide +kernel
theorem block000_data_flat136_original : block000_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) := by
  rw [block000_data_flat136_step, block000_data_flat126_original, block000_data_flat135_original]
def block000_data_flat137 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 6480))]
theorem block000_data_flat137_step : block000_data_flat137 = (CoefficientMerge.scale (6480 : Int) atom0070Coded) := by decide +kernel
theorem block000_data_flat137_original : block000_data_flat137 = (CoefficientMerge.scale (6480 : Int) atom0070Coded) := by
  rw [block000_data_flat137_step]
def block000_data_flat138 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 287280))]
theorem block000_data_flat138_step : block000_data_flat138 = (CoefficientMerge.scale (287280 : Int) atom0071Coded) := by decide +kernel
theorem block000_data_flat138_original : block000_data_flat138 = (CoefficientMerge.scale (287280 : Int) atom0071Coded) := by
  rw [block000_data_flat138_step]
def block000_data_flat139 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280))]
theorem block000_data_flat139_step : block000_data_flat139 = (CoefficientMerge.fastMerge block000_data_flat137 block000_data_flat138) := by decide +kernel
theorem block000_data_flat139_original : block000_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) := by
  rw [block000_data_flat139_step, block000_data_flat137_original, block000_data_flat138_original]
def block000_data_flat140 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 88560))]
theorem block000_data_flat140_step : block000_data_flat140 = (CoefficientMerge.scale (88560 : Int) atom0072Coded) := by decide +kernel
theorem block000_data_flat140_original : block000_data_flat140 = (CoefficientMerge.scale (88560 : Int) atom0072Coded) := by
  rw [block000_data_flat140_step]
def block000_data_flat141 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 158760))]
theorem block000_data_flat141_step : block000_data_flat141 = (CoefficientMerge.scale (158760 : Int) atom0073Coded) := by decide +kernel
theorem block000_data_flat141_original : block000_data_flat141 = (CoefficientMerge.scale (158760 : Int) atom0073Coded) := by
  rw [block000_data_flat141_step]
def block000_data_flat142 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 157680))]
theorem block000_data_flat142_step : block000_data_flat142 = (CoefficientMerge.scale (157680 : Int) atom0074Coded) := by decide +kernel
theorem block000_data_flat142_original : block000_data_flat142 = (CoefficientMerge.scale (157680 : Int) atom0074Coded) := by
  rw [block000_data_flat142_step]
def block000_data_flat143 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680))]
theorem block000_data_flat143_step : block000_data_flat143 = (CoefficientMerge.fastMerge block000_data_flat141 block000_data_flat142) := by decide +kernel
theorem block000_data_flat143_original : block000_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)) := by
  rw [block000_data_flat143_step, block000_data_flat141_original, block000_data_flat142_original]
def block000_data_flat144 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680))]
theorem block000_data_flat144_step : block000_data_flat144 = (CoefficientMerge.fastMerge block000_data_flat140 block000_data_flat143) := by decide +kernel
theorem block000_data_flat144_original : block000_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded))) := by
  rw [block000_data_flat144_step, block000_data_flat140_original, block000_data_flat143_original]
def block000_data_flat145 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680))]
theorem block000_data_flat145_step : block000_data_flat145 = (CoefficientMerge.fastMerge block000_data_flat139 block000_data_flat144) := by decide +kernel
theorem block000_data_flat145_original : block000_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) := by
  rw [block000_data_flat145_step, block000_data_flat139_original, block000_data_flat144_original]
def block000_data_flat146 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 226800))]
theorem block000_data_flat146_step : block000_data_flat146 = (CoefficientMerge.scale (226800 : Int) atom0075Coded) := by decide +kernel
theorem block000_data_flat146_original : block000_data_flat146 = (CoefficientMerge.scale (226800 : Int) atom0075Coded) := by
  rw [block000_data_flat146_step]
def block000_data_flat147 : CoefficientMerge.Poly := [(nat_lit 192, Int.ofNat (nat_lit 479520))]
theorem block000_data_flat147_step : block000_data_flat147 = (CoefficientMerge.scale (479520 : Int) atom0076Coded) := by decide +kernel
theorem block000_data_flat147_original : block000_data_flat147 = (CoefficientMerge.scale (479520 : Int) atom0076Coded) := by
  rw [block000_data_flat147_step]
def block000_data_flat148 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520))]
theorem block000_data_flat148_step : block000_data_flat148 = (CoefficientMerge.fastMerge block000_data_flat146 block000_data_flat147) := by decide +kernel
theorem block000_data_flat148_original : block000_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) := by
  rw [block000_data_flat148_step, block000_data_flat146_original, block000_data_flat147_original]
def block000_data_flat149 : CoefficientMerge.Poly := [(nat_lit 193, Int.ofNat (nat_lit 671760))]
theorem block000_data_flat149_step : block000_data_flat149 = (CoefficientMerge.scale (671760 : Int) atom0077Coded) := by decide +kernel
theorem block000_data_flat149_original : block000_data_flat149 = (CoefficientMerge.scale (671760 : Int) atom0077Coded) := by
  rw [block000_data_flat149_step]
def block000_data_flat150 : CoefficientMerge.Poly := [(nat_lit 194, Int.ofNat (nat_lit 922320))]
theorem block000_data_flat150_step : block000_data_flat150 = (CoefficientMerge.scale (922320 : Int) atom0078Coded) := by decide +kernel
theorem block000_data_flat150_original : block000_data_flat150 = (CoefficientMerge.scale (922320 : Int) atom0078Coded) := by
  rw [block000_data_flat150_step]
def block000_data_flat151 : CoefficientMerge.Poly := [(nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat151_step : block000_data_flat151 = (CoefficientMerge.scale (1030320 : Int) atom0079Coded) := by decide +kernel
theorem block000_data_flat151_original : block000_data_flat151 = (CoefficientMerge.scale (1030320 : Int) atom0079Coded) := by
  rw [block000_data_flat151_step]
def block000_data_flat152 : CoefficientMerge.Poly := [(nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat152_step : block000_data_flat152 = (CoefficientMerge.fastMerge block000_data_flat150 block000_data_flat151) := by decide +kernel
theorem block000_data_flat152_original : block000_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)) := by
  rw [block000_data_flat152_step, block000_data_flat150_original, block000_data_flat151_original]
def block000_data_flat153 : CoefficientMerge.Poly := [(nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat153_step : block000_data_flat153 = (CoefficientMerge.fastMerge block000_data_flat149 block000_data_flat152) := by decide +kernel
theorem block000_data_flat153_original : block000_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded))) := by
  rw [block000_data_flat153_step, block000_data_flat149_original, block000_data_flat152_original]
def block000_data_flat154 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat154_step : block000_data_flat154 = (CoefficientMerge.fastMerge block000_data_flat148 block000_data_flat153) := by decide +kernel
theorem block000_data_flat154_original : block000_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)))) := by
  rw [block000_data_flat154_step, block000_data_flat148_original, block000_data_flat153_original]
def block000_data_flat155 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat155_step : block000_data_flat155 = (CoefficientMerge.fastMerge block000_data_flat145 block000_data_flat154) := by decide +kernel
theorem block000_data_flat155_original : block000_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded))))) := by
  rw [block000_data_flat155_step, block000_data_flat145_original, block000_data_flat154_original]
def block000_data_flat156 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830)), (nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat156_step : block000_data_flat156 = (CoefficientMerge.fastMerge block000_data_flat136 block000_data_flat155) := by decide +kernel
theorem block000_data_flat156_original : block000_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)))))) := by
  rw [block000_data_flat156_step, block000_data_flat136_original, block000_data_flat155_original]
def block000_data_flat157 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200)), (nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770)), (nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830)), (nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat157_step : block000_data_flat157 = (CoefficientMerge.fastMerge block000_data_flat117 block000_data_flat156) := by decide +kernel
theorem block000_data_flat157_original : block000_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded))))))) := by
  rw [block000_data_flat157_step, block000_data_flat117_original, block000_data_flat156_original]
def block000_data_flat158 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540)), (nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120)), (nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880)), (nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280)), (nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200)), (nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770)), (nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830)), (nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat158_step : block000_data_flat158 = (CoefficientMerge.fastMerge block000_data_flat078 block000_data_flat157) := by decide +kernel
theorem block000_data_flat158_original : block000_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)))))))) := by
  rw [block000_data_flat158_step, block000_data_flat078_original, block000_data_flat157_original]
def block000_data_flat159 : CoefficientMerge.Poly := [(nat_lit 3, Int.ofNat (nat_lit 120240)), (nat_lit 4, Int.ofNat (nat_lit 95040)), (nat_lit 5, Int.ofNat (nat_lit 69840)), (nat_lit 6, Int.ofNat (nat_lit 44640)), (nat_lit 10, Int.ofNat (nat_lit 27240)), (nat_lit 11, Int.ofNat (nat_lit 175680)), (nat_lit 12, Int.ofNat (nat_lit 481140)), (nat_lit 13, Int.ofNat (nat_lit 229160)), (nat_lit 14, Int.ofNat (nat_lit 126540)), (nat_lit 15, Int.ofNat (nat_lit 81540)), (nat_lit 16, Int.ofNat (nat_lit 45520)), (nat_lit 20, Int.ofNat (nat_lit 219600)), (nat_lit 21, Int.ofNat (nat_lit 731160)), (nat_lit 22, Int.ofNat (nat_lit 477000)), (nat_lit 23, Int.ofNat (nat_lit 313380)), (nat_lit 24, Int.ofNat (nat_lit 158040)), (nat_lit 25, Int.ofNat (nat_lit 139500)), (nat_lit 26, Int.ofNat (nat_lit 34200)), (nat_lit 30, Int.ofNat (nat_lit 508320)), (nat_lit 31, Int.ofNat (nat_lit 843120)), (nat_lit 32, Int.ofNat (nat_lit 804060)), (nat_lit 33, Int.ofNat (nat_lit 729360)), (nat_lit 34, Int.ofNat (nat_lit 344700)), (nat_lit 35, Int.ofNat (nat_lit 388080)), (nat_lit 40, Int.ofNat (nat_lit 382464)), (nat_lit 41, Int.ofNat (nat_lit 715680)), (nat_lit 42, Int.ofNat (nat_lit 812160)), (nat_lit 43, Int.ofNat (nat_lit 436500)), (nat_lit 44, Int.ofNat (nat_lit 544320)), (nat_lit 50, Int.ofNat (nat_lit 380880)), (nat_lit 51, Int.ofNat (nat_lit 894960)), (nat_lit 52, Int.ofNat (nat_lit 500580)), (nat_lit 53, Int.ofNat (nat_lit 470160)), (nat_lit 60, Int.ofNat (nat_lit 488880)), (nat_lit 61, Int.ofNat (nat_lit 592380)), (nat_lit 62, Int.ofNat (nat_lit 626400)), (nat_lit 70, Int.ofNat (nat_lit 60300)), (nat_lit 71, Int.ofNat (nat_lit 110700)), (nat_lit 91, Int.ofNat (nat_lit 360)), (nat_lit 92, Int.ofNat (nat_lit 11280)), (nat_lit 93, Int.ofNat (nat_lit 209940)), (nat_lit 96, Int.ofNat (nat_lit 1380)), (nat_lit 101, Int.ofNat (nat_lit 12960)), (nat_lit 102, Int.ofNat (nat_lit 538560)), (nat_lit 103, Int.ofNat (nat_lit 223280)), (nat_lit 104, Int.ofNat (nat_lit 334260)), (nat_lit 105, Int.ofNat (nat_lit 443520)), (nat_lit 106, Int.ofNat (nat_lit 404920)), (nat_lit 107, Int.ofNat (nat_lit 560400)), (nat_lit 111, Int.ofNat (nat_lit 475200)), (nat_lit 112, Int.ofNat (nat_lit 655960)), (nat_lit 113, Int.ofNat (nat_lit 892980)), (nat_lit 114, Int.ofNat (nat_lit 1075680)), (nat_lit 115, Int.ofNat (nat_lit 559400)), (nat_lit 116, Int.ofNat (nat_lit 745140)), (nat_lit 121, Int.ofNat (nat_lit 213356)), (nat_lit 122, Int.ofNat (nat_lit 591100)), (nat_lit 123, Int.ofNat (nat_lit 968550)), (nat_lit 124, Int.ofNat (nat_lit 700670)), (nat_lit 125, Int.ofNat (nat_lit 874770)), (nat_lit 131, Int.ofNat (nat_lit 489240)), (nat_lit 132, Int.ofNat (nat_lit 975960)), (nat_lit 133, Int.ofNat (nat_lit 743780)), (nat_lit 134, Int.ofNat (nat_lit 978960)), (nat_lit 141, Int.ofNat (nat_lit 436320)), (nat_lit 142, Int.ofNat (nat_lit 697890)), (nat_lit 143, Int.ofNat (nat_lit 989850)), (nat_lit 151, Int.ofNat (nat_lit 179150)), (nat_lit 152, Int.ofNat (nat_lit 626340)), (nat_lit 161, Int.ofNat (nat_lit 331830)), (nat_lit 182, Int.ofNat (nat_lit 6480)), (nat_lit 183, Int.ofNat (nat_lit 287280)), (nat_lit 184, Int.ofNat (nat_lit 88560)), (nat_lit 185, Int.ofNat (nat_lit 158760)), (nat_lit 186, Int.ofNat (nat_lit 157680)), (nat_lit 188, Int.ofNat (nat_lit 226800)), (nat_lit 192, Int.ofNat (nat_lit 479520)), (nat_lit 193, Int.ofNat (nat_lit 671760)), (nat_lit 194, Int.ofNat (nat_lit 922320)), (nat_lit 195, Int.ofNat (nat_lit 1030320))]
theorem block000_data_flat159_step : block000_data_flat159 = (CoefficientMerge.trim block000_data_flat158) := by decide +kernel
theorem block000_data_flat159_original : block000_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded))))))))) := by
  rw [block000_data_flat159_step, block000_data_flat158_original]
theorem block000_data : block000 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120240 : Int) atom0000Coded) (CoefficientMerge.scale (95040 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69840 : Int) atom0002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44640 : Int) atom0003Coded) (CoefficientMerge.scale (27240 : Int) atom0004Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175680 : Int) atom0005Coded) (CoefficientMerge.scale (481140 : Int) atom0006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229160 : Int) atom0007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126540 : Int) atom0008Coded) (CoefficientMerge.scale (81540 : Int) atom0009Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45520 : Int) atom0010Coded) (CoefficientMerge.scale (219600 : Int) atom0011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731160 : Int) atom0012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477000 : Int) atom0013Coded) (CoefficientMerge.scale (313380 : Int) atom0014Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158040 : Int) atom0015Coded) (CoefficientMerge.scale (139500 : Int) atom0016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34200 : Int) atom0017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508320 : Int) atom0018Coded) (CoefficientMerge.scale (843120 : Int) atom0019Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804060 : Int) atom0020Coded) (CoefficientMerge.scale (729360 : Int) atom0021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344700 : Int) atom0022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (388080 : Int) atom0023Coded) (CoefficientMerge.scale (382464 : Int) atom0024Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (715680 : Int) atom0025Coded) (CoefficientMerge.scale (812160 : Int) atom0026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436500 : Int) atom0027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (544320 : Int) atom0028Coded) (CoefficientMerge.scale (380880 : Int) atom0029Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (894960 : Int) atom0030Coded) (CoefficientMerge.scale (500580 : Int) atom0031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (470160 : Int) atom0032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488880 : Int) atom0033Coded) (CoefficientMerge.scale (592380 : Int) atom0034Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (626400 : Int) atom0035Coded) (CoefficientMerge.scale (60300 : Int) atom0036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110700 : Int) atom0037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0038Coded) (CoefficientMerge.scale (11280 : Int) atom0039Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (209940 : Int) atom0040Coded) (CoefficientMerge.scale (1380 : Int) atom0041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12960 : Int) atom0042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538560 : Int) atom0043Coded) (CoefficientMerge.scale (223280 : Int) atom0044Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (334260 : Int) atom0045Coded) (CoefficientMerge.scale (443520 : Int) atom0046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (404920 : Int) atom0047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (560400 : Int) atom0048Coded) (CoefficientMerge.scale (475200 : Int) atom0049Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (655960 : Int) atom0050Coded) (CoefficientMerge.scale (892980 : Int) atom0051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1075680 : Int) atom0052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (559400 : Int) atom0053Coded) (CoefficientMerge.scale (745140 : Int) atom0054Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213356 : Int) atom0055Coded) (CoefficientMerge.scale (591100 : Int) atom0056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (968550 : Int) atom0057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (700670 : Int) atom0058Coded) (CoefficientMerge.scale (874770 : Int) atom0059Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (489240 : Int) atom0060Coded) (CoefficientMerge.scale (975960 : Int) atom0061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743780 : Int) atom0062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (978960 : Int) atom0063Coded) (CoefficientMerge.scale (436320 : Int) atom0064Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (697890 : Int) atom0065Coded) (CoefficientMerge.scale (989850 : Int) atom0066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179150 : Int) atom0067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626340 : Int) atom0068Coded) (CoefficientMerge.scale (331830 : Int) atom0069Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6480 : Int) atom0070Coded) (CoefficientMerge.scale (287280 : Int) atom0071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88560 : Int) atom0072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158760 : Int) atom0073Coded) (CoefficientMerge.scale (157680 : Int) atom0074Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226800 : Int) atom0075Coded) (CoefficientMerge.scale (479520 : Int) atom0076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671760 : Int) atom0077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (922320 : Int) atom0078Coded) (CoefficientMerge.scale (1030320 : Int) atom0079Coded)))))))) := by
  have h : block000 = block000_data_flat159 := by decide +kernel
  exact h.trans block000_data_flat159_original
theorem block000_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) block000 := by
  rw [block000_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000Coded_nonneg g hg hA hB) (atom0001Coded_nonneg g hg hA hB)) (add_nonneg (atom0002Coded_nonneg g hg hA hB) (add_nonneg (atom0003Coded_nonneg g hg hA hB) (atom0004Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0005Coded_nonneg g hg hA hB) (atom0006Coded_nonneg g hg hA hB)) (add_nonneg (atom0007Coded_nonneg g hg hA hB) (add_nonneg (atom0008Coded_nonneg g hg hA hB) (atom0009Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0010Coded_nonneg g hg hA hB) (atom0011Coded_nonneg g hg hA hB)) (add_nonneg (atom0012Coded_nonneg g hg hA hB) (add_nonneg (atom0013Coded_nonneg g hg hA hB) (atom0014Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0015Coded_nonneg g hg hA hB) (atom0016Coded_nonneg g hg hA hB)) (add_nonneg (atom0017Coded_nonneg g hg hA hB) (add_nonneg (atom0018Coded_nonneg g hg hA hB) (atom0019Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0020Coded_nonneg g hg hA hB) (atom0021Coded_nonneg g hg hA hB)) (add_nonneg (atom0022Coded_nonneg g hg hA hB) (add_nonneg (atom0023Coded_nonneg g hg hA hB) (atom0024Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0025Coded_nonneg g hg hA hB) (atom0026Coded_nonneg g hg hA hB)) (add_nonneg (atom0027Coded_nonneg g hg hA hB) (add_nonneg (atom0028Coded_nonneg g hg hA hB) (atom0029Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0030Coded_nonneg g hg hA hB) (atom0031Coded_nonneg g hg hA hB)) (add_nonneg (atom0032Coded_nonneg g hg hA hB) (add_nonneg (atom0033Coded_nonneg g hg hA hB) (atom0034Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0035Coded_nonneg g hg hA hB) (atom0036Coded_nonneg g hg hA hB)) (add_nonneg (atom0037Coded_nonneg g hg hA hB) (add_nonneg (atom0038Coded_nonneg g hg hA hB) (atom0039Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0040Coded_nonneg g hg hA hB) (atom0041Coded_nonneg g hg hA hB)) (add_nonneg (atom0042Coded_nonneg g hg hA hB) (add_nonneg (atom0043Coded_nonneg g hg hA hB) (atom0044Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0045Coded_nonneg g hg hA hB) (atom0046Coded_nonneg g hg hA hB)) (add_nonneg (atom0047Coded_nonneg g hg hA hB) (add_nonneg (atom0048Coded_nonneg g hg hA hB) (atom0049Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0050Coded_nonneg g hg hA hB) (atom0051Coded_nonneg g hg hA hB)) (add_nonneg (atom0052Coded_nonneg g hg hA hB) (add_nonneg (atom0053Coded_nonneg g hg hA hB) (atom0054Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0055Coded_nonneg g hg hA hB) (atom0056Coded_nonneg g hg hA hB)) (add_nonneg (atom0057Coded_nonneg g hg hA hB) (add_nonneg (atom0058Coded_nonneg g hg hA hB) (atom0059Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0060Coded_nonneg g hg hA hB) (atom0061Coded_nonneg g hg hA hB)) (add_nonneg (atom0062Coded_nonneg g hg hA hB) (add_nonneg (atom0063Coded_nonneg g hg hA hB) (atom0064Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0065Coded_nonneg g hg hA hB) (atom0066Coded_nonneg g hg hA hB)) (add_nonneg (atom0067Coded_nonneg g hg hA hB) (add_nonneg (atom0068Coded_nonneg g hg hA hB) (atom0069Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0070Coded_nonneg g hg hA hB) (atom0071Coded_nonneg g hg hA hB)) (add_nonneg (atom0072Coded_nonneg g hg hA hB) (add_nonneg (atom0073Coded_nonneg g hg hA hB) (atom0074Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0075Coded_nonneg g hg hA hB) (atom0076Coded_nonneg g hg hA hB)) (add_nonneg (atom0077Coded_nonneg g hg hA hB) (add_nonneg (atom0078Coded_nonneg g hg hA hB) (atom0079Coded_nonneg g hg hA hB))))))))

end APPT.Finite9
