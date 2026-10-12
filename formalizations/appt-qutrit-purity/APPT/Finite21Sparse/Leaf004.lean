-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0176 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0176 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5302217692800 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176Coded : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 1))]
theorem atom0176Coded_decode : atom0176 = SparsePolynomial.decodeCubic 21 atom0176Coded := by decide +kernel
theorem atom0176Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) := by
  have h := atom0176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0177 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0177 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1801017590400 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177Coded : CoefficientMerge.Poly := [(nat_lit 38, Int.ofNat (nat_lit 1))]
theorem atom0177Coded_decode : atom0177 = SparsePolynomial.decodeCubic 21 atom0177Coded := by decide +kernel
theorem atom0177Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded) := by
  have h := atom0177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0178 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0178 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (787190140800 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178Coded : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 1))]
theorem atom0178Coded_decode : atom0178 = SparsePolynomial.decodeCubic 21 atom0178Coded := by decide +kernel
theorem atom0178Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) := by
  have h := atom0178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0179 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (420253545600 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179Coded : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 1))]
theorem atom0179Coded_decode : atom0179 = SparsePolynomial.decodeCubic 21 atom0179Coded := by decide +kernel
theorem atom0179Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) := by
  have h := atom0179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0180 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0180 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7838074944000 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180Coded : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 1))]
theorem atom0180Coded_decode : atom0180 = SparsePolynomial.decodeCubic 21 atom0180Coded := by decide +kernel
theorem atom0180Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded) := by
  have h := atom0180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0181 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0181 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16012481587200 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181Coded : CoefficientMerge.Poly := [(nat_lit 45, Int.ofNat (nat_lit 1))]
theorem atom0181Coded_decode : atom0181 = SparsePolynomial.decodeCubic 21 atom0181Coded := by decide +kernel
theorem atom0181Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) := by
  have h := atom0181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0182 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0182 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16348813286400 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182Coded : CoefficientMerge.Poly := [(nat_lit 46, Int.ofNat (nat_lit 1))]
theorem atom0182Coded_decode : atom0182 = SparsePolynomial.decodeCubic 21 atom0182Coded := by decide +kernel
theorem atom0182Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded) := by
  have h := atom0182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0183 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16685144985600 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183Coded : CoefficientMerge.Poly := [(nat_lit 47, Int.ofNat (nat_lit 1))]
theorem atom0183Coded_decode : atom0183 = SparsePolynomial.decodeCubic 21 atom0183Coded := by decide +kernel
theorem atom0183Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) := by
  have h := atom0183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0184 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0184 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17021476684800 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184Coded : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 1))]
theorem atom0184Coded_decode : atom0184 = SparsePolynomial.decodeCubic 21 atom0184Coded := by decide +kernel
theorem atom0184Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) := by
  have h := atom0184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0185 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0185 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17357808384000 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185Coded : CoefficientMerge.Poly := [(nat_lit 49, Int.ofNat (nat_lit 1))]
theorem atom0185Coded_decode : atom0185 = SparsePolynomial.decodeCubic 21 atom0185Coded := by decide +kernel
theorem atom0185Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded) := by
  have h := atom0185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0186 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17694140083200 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186Coded : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 1))]
theorem atom0186Coded_decode : atom0186 = SparsePolynomial.decodeCubic 21 atom0186Coded := by decide +kernel
theorem atom0186Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) := by
  have h := atom0186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0187 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18030471782400 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187Coded : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 1))]
theorem atom0187Coded_decode : atom0187 = SparsePolynomial.decodeCubic 21 atom0187Coded := by decide +kernel
theorem atom0187Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded) := by
  have h := atom0187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0188 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18366803481600 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188Coded : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 1))]
theorem atom0188Coded_decode : atom0188 = SparsePolynomial.decodeCubic 21 atom0188Coded := by decide +kernel
theorem atom0188Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) := by
  have h := atom0188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0189 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18703135180800 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189Coded : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 1))]
theorem atom0189Coded_decode : atom0189 = SparsePolynomial.decodeCubic 21 atom0189Coded := by decide +kernel
theorem atom0189Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) := by
  have h := atom0189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0190 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19039466880000 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190Coded : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 1))]
theorem atom0190Coded_decode : atom0190 = SparsePolynomial.decodeCubic 21 atom0190Coded := by decide +kernel
theorem atom0190Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded) := by
  have h := atom0190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0191 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19375798579200 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191Coded : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 1))]
theorem atom0191Coded_decode : atom0191 = SparsePolynomial.decodeCubic 21 atom0191Coded := by decide +kernel
theorem atom0191Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) := by
  have h := atom0191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0192 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19712130278400 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192Coded : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 1))]
theorem atom0192Coded_decode : atom0192 = SparsePolynomial.decodeCubic 21 atom0192Coded := by decide +kernel
theorem atom0192Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded) := by
  have h := atom0192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0193 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22980733171200 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193Coded : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 1))]
theorem atom0193Coded_decode : atom0193 = SparsePolynomial.decodeCubic 21 atom0193Coded := by decide +kernel
theorem atom0193Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) := by
  have h := atom0193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0194 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0194 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13269638592000 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194Coded : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 1))]
theorem atom0194Coded_decode : atom0194 = SparsePolynomial.decodeCubic 21 atom0194Coded := by decide +kernel
theorem atom0194Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) := by
  have h := atom0194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0195 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0195 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10896850944000 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195Coded : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 1))]
theorem atom0195Coded_decode : atom0195 = SparsePolynomial.decodeCubic 21 atom0195Coded := by decide +kernel
theorem atom0195Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded) := by
  have h := atom0195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0196 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0196 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1702920844800 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196Coded : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1))]
theorem atom0196Coded_decode : atom0196 = SparsePolynomial.decodeCubic 21 atom0196Coded := by decide +kernel
theorem atom0196Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) := by
  have h := atom0196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0197 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0197 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2888296790400 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197Coded : CoefficientMerge.Poly := [(nat_lit 61, Int.ofNat (nat_lit 1))]
theorem atom0197Coded_decode : atom0197 = SparsePolynomial.decodeCubic 21 atom0197Coded := by decide +kernel
theorem atom0197Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded) := by
  have h := atom0197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0198 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0198 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7747226726400 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198Coded : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 1))]
theorem atom0198Coded_decode : atom0198 = SparsePolynomial.decodeCubic 21 atom0198Coded := by decide +kernel
theorem atom0198Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) := by
  have h := atom0198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0199 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0199 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15998951001600 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199Coded : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 1))]
theorem atom0199Coded_decode : atom0199 = SparsePolynomial.decodeCubic 21 atom0199Coded := by decide +kernel
theorem atom0199Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) := by
  have h := atom0199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0200 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0200 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16503448550400 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200Coded : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 1))]
theorem atom0200Coded_decode : atom0200 = SparsePolynomial.decodeCubic 21 atom0200Coded := by decide +kernel
theorem atom0200Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded) := by
  have h := atom0200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0201 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0201 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17007946099200 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201Coded : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 1))]
theorem atom0201Coded_decode : atom0201 = SparsePolynomial.decodeCubic 21 atom0201Coded := by decide +kernel
theorem atom0201Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) := by
  have h := atom0201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0202 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17512443648000 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202Coded : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 1))]
theorem atom0202Coded_decode : atom0202 = SparsePolynomial.decodeCubic 21 atom0202Coded := by decide +kernel
theorem atom0202Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded) := by
  have h := atom0202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0203 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0203 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18016941196800 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203Coded : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 1))]
theorem atom0203Coded_decode : atom0203 = SparsePolynomial.decodeCubic 21 atom0203Coded := by decide +kernel
theorem atom0203Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) := by
  have h := atom0203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0204 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0204 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18521438745600 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204Coded : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 1))]
theorem atom0204Coded_decode : atom0204 = SparsePolynomial.decodeCubic 21 atom0204Coded := by decide +kernel
theorem atom0204Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) := by
  have h := atom0204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0205 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0205 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19025936294400 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205Coded : CoefficientMerge.Poly := [(nat_lit 73, Int.ofNat (nat_lit 1))]
theorem atom0205Coded_decode : atom0205 = SparsePolynomial.decodeCubic 21 atom0205Coded := by decide +kernel
theorem atom0205Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded) := by
  have h := atom0205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0206 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0206 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19530433843200 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206Coded : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 1))]
theorem atom0206Coded_decode : atom0206 = SparsePolynomial.decodeCubic 21 atom0206Coded := by decide +kernel
theorem atom0206Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) := by
  have h := atom0206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0207 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0207 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20034931392000 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207Coded : CoefficientMerge.Poly := [(nat_lit 75, Int.ofNat (nat_lit 1))]
theorem atom0207Coded_decode : atom0207 = SparsePolynomial.decodeCubic 21 atom0207Coded := by decide +kernel
theorem atom0207Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded) := by
  have h := atom0207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0208 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0208 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20539428940800 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208Coded : CoefficientMerge.Poly := [(nat_lit 76, Int.ofNat (nat_lit 1))]
theorem atom0208Coded_decode : atom0208 = SparsePolynomial.decodeCubic 21 atom0208Coded := by decide +kernel
theorem atom0208Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) := by
  have h := atom0208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0209 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0209 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21043926489600 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209Coded : CoefficientMerge.Poly := [(nat_lit 77, Int.ofNat (nat_lit 1))]
theorem atom0209Coded_decode : atom0209 = SparsePolynomial.decodeCubic 21 atom0209Coded := by decide +kernel
theorem atom0209Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) := by
  have h := atom0209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0210 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0210 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24373900252800 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210Coded : CoefficientMerge.Poly := [(nat_lit 78, Int.ofNat (nat_lit 1))]
theorem atom0210Coded_decode : atom0210 = SparsePolynomial.decodeCubic 21 atom0210Coded := by decide +kernel
theorem atom0210Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded) := by
  have h := atom0210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0211 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0211 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15288112022400 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211Coded : CoefficientMerge.Poly := [(nat_lit 79, Int.ofNat (nat_lit 1))]
theorem atom0211Coded_decode : atom0211 = SparsePolynomial.decodeCubic 21 atom0211Coded := by decide +kernel
theorem atom0211Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) := by
  have h := atom0211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0212 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11985579849600 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212Coded : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 1))]
theorem atom0212Coded_decode : atom0212 = SparsePolynomial.decodeCubic 21 atom0212Coded := by decide +kernel
theorem atom0212Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded) := by
  have h := atom0212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0213 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0213 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = ((g 0) * (g 3) * (g 18)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3766818384000 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213Coded : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 1))]
theorem atom0213Coded_decode : atom0213 = SparsePolynomial.decodeCubic 21 atom0213Coded := by decide +kernel
theorem atom0213Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) := by
  have h := atom0213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0214 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0214 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = ((g 0) * (g 3) * (g 19)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5075419305600 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214Coded : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 1))]
theorem atom0214Coded_decode : atom0214 = SparsePolynomial.decodeCubic 21 atom0214Coded := by decide +kernel
theorem atom0214Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) := by
  have h := atom0214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0215 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0215 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = ((g 0) * (g 3) * (g 20)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389970806400 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215Coded : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 1))]
theorem atom0215Coded_decode : atom0215 = SparsePolynomial.decodeCubic 21 atom0215Coded := by decide +kernel
theorem atom0215Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded) := by
  have h := atom0215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0216 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0216 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8898776208000 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216Coded : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 1))]
theorem atom0216Coded_decode : atom0216 = SparsePolynomial.decodeCubic 21 atom0216Coded := by decide +kernel
theorem atom0216Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) := by
  have h := atom0216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0217 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0217 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16329426810624 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217Coded : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 1))]
theorem atom0217Coded_decode : atom0217 = SparsePolynomial.decodeCubic 21 atom0217Coded := by decide +kernel
theorem atom0217Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded) := by
  have h := atom0217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0218 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0218 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16994415513600 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218Coded : CoefficientMerge.Poly := [(nat_lit 90, Int.ofNat (nat_lit 1))]
theorem atom0218Coded_decode : atom0218 = SparsePolynomial.decodeCubic 21 atom0218Coded := by decide +kernel
theorem atom0218Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) := by
  have h := atom0218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0219 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0219 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17667078912000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219Coded : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 1))]
theorem atom0219Coded_decode : atom0219 = SparsePolynomial.decodeCubic 21 atom0219Coded := by decide +kernel
theorem atom0219Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) := by
  have h := atom0219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0220 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0220 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18339742310400 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220Coded : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 1))]
theorem atom0220Coded_decode : atom0220 = SparsePolynomial.decodeCubic 21 atom0220Coded := by decide +kernel
theorem atom0220Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded) := by
  have h := atom0220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0221 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0221 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19012405708800 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221Coded : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 1))]
theorem atom0221Coded_decode : atom0221 = SparsePolynomial.decodeCubic 21 atom0221Coded := by decide +kernel
theorem atom0221Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) := by
  have h := atom0221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0222 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0222 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19685069107200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222Coded : CoefficientMerge.Poly := [(nat_lit 94, Int.ofNat (nat_lit 1))]
theorem atom0222Coded_decode : atom0222 = SparsePolynomial.decodeCubic 21 atom0222Coded := by decide +kernel
theorem atom0222Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded) := by
  have h := atom0222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0223 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0223 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20357732505600 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223Coded : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 1))]
theorem atom0223Coded_decode : atom0223 = SparsePolynomial.decodeCubic 21 atom0223Coded := by decide +kernel
theorem atom0223Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) := by
  have h := atom0223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0224 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0224 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21233148865600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224Coded : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 1))]
theorem atom0224Coded_decode : atom0224 = SparsePolynomial.decodeCubic 21 atom0224Coded := by decide +kernel
theorem atom0224Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) := by
  have h := atom0224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0225 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0225 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22067177025600 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225Coded : CoefficientMerge.Poly := [(nat_lit 97, Int.ofNat (nat_lit 1))]
theorem atom0225Coded_decode : atom0225 = SparsePolynomial.decodeCubic 21 atom0225Coded := by decide +kernel
theorem atom0225Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded) := by
  have h := atom0225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0226 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0226 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22681852200000 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226Coded : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 1))]
theorem atom0226Coded_decode : atom0226 = SparsePolynomial.decodeCubic 21 atom0226Coded := by decide +kernel
theorem atom0226Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) := by
  have h := atom0226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0227 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0227 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25767067334400 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227Coded : CoefficientMerge.Poly := [(nat_lit 99, Int.ofNat (nat_lit 1))]
theorem atom0227Coded_decode : atom0227 = SparsePolynomial.decodeCubic 21 atom0227Coded := by decide +kernel
theorem atom0227Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded) := by
  have h := atom0227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0228 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0228 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17557535532600 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228Coded : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 1))]
theorem atom0228Coded_decode : atom0228 = SparsePolynomial.decodeCubic 21 atom0228Coded := by decide +kernel
theorem atom0228Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) := by
  have h := atom0228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0229 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0229 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13074308755200 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229Coded : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 1))]
theorem atom0229Coded_decode : atom0229 = SparsePolynomial.decodeCubic 21 atom0229Coded := by decide +kernel
theorem atom0229Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) := by
  have h := atom0229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0230 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0230 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 0) * (g 4) * (g 18)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6011898921000 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230Coded : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 1))]
theorem atom0230Coded_decode : atom0230 = SparsePolynomial.decodeCubic 21 atom0230Coded := by decide +kernel
theorem atom0230Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded) := by
  have h := atom0230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0231 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0231 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 0) * (g 4) * (g 19)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7268672867400 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231Coded : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 1))]
theorem atom0231Coded_decode : atom0231 = SparsePolynomial.decodeCubic 21 atom0231Coded := by decide +kernel
theorem atom0231Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) := by
  have h := atom0231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0232 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0232 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 0) * (g 4) * (g 20)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2531397393000 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232Coded : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 1))]
theorem atom0232Coded_decode : atom0232 = SparsePolynomial.decodeCubic 21 atom0232Coded := by decide +kernel
theorem atom0232Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded) := by
  have h := atom0232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0233 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0233 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10430034421248 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 1))]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 21 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0234 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18863725537728 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 1))]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 21 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0235 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18055888573248 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 1))]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 21 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0236 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18662543424000 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 1))]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 21 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0237 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19685793960000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1))]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 21 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0238 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20344201920000 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 1))]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 21 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0239 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21185031168000 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 1))]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 21 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0240 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0240 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22373100702400 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240Coded : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 1))]
theorem atom0240Coded_decode : atom0240 = SparsePolynomial.decodeCubic 21 atom0240Coded := by decide +kernel
theorem atom0240Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded) := by
  have h := atom0240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0241 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0241 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23206404009600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241Coded : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 1))]
theorem atom0241Coded_decode : atom0241 = SparsePolynomial.decodeCubic 21 atom0241Coded := by decide +kernel
theorem atom0241Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) := by
  have h := atom0241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0242 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0242 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23885832700800 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242Coded : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 1))]
theorem atom0242Coded_decode : atom0242 = SparsePolynomial.decodeCubic 21 atom0242Coded := by decide +kernel
theorem atom0242Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded) := by
  have h := atom0242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0243 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0243 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27533078906688 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243Coded : CoefficientMerge.Poly := [(nat_lit 120, Int.ofNat (nat_lit 1))]
theorem atom0243Coded_decode : atom0243 = SparsePolynomial.decodeCubic 21 atom0243Coded := by decide +kernel
theorem atom0243Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) := by
  have h := atom0243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0244 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0244 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19930254363648 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244Coded : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 1))]
theorem atom0244Coded_decode : atom0244 = SparsePolynomial.decodeCubic 21 atom0244Coded := by decide +kernel
theorem atom0244Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) := by
  have h := atom0244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0245 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0245 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16772949095616 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245Coded : CoefficientMerge.Poly := [(nat_lit 122, Int.ofNat (nat_lit 1))]
theorem atom0245Coded_decode : atom0245 = SparsePolynomial.decodeCubic 21 atom0245Coded := by decide +kernel
theorem atom0245Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded) := by
  have h := atom0245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0246 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0246 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 0) * (g 5) * (g 18)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10592587378944 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246Coded : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 1))]
theorem atom0246Coded_decode : atom0246 = SparsePolynomial.decodeCubic 21 atom0246Coded := by decide +kernel
theorem atom0246Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) := by
  have h := atom0246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0247 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0247 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 0) * (g 5) * (g 19)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11062689626880 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247Coded : CoefficientMerge.Poly := [(nat_lit 124, Int.ofNat (nat_lit 1))]
theorem atom0247Coded_decode : atom0247 = SparsePolynomial.decodeCubic 21 atom0247Coded := by decide +kernel
theorem atom0247Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded) := by
  have h := atom0247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0248 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0248 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 0) * (g 5) * (g 20)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7775809398144 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248Coded : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 1))]
theorem atom0248Coded_decode : atom0248 = SparsePolynomial.decodeCubic 21 atom0248Coded := by decide +kernel
theorem atom0248Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) := by
  have h := atom0248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0249 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0249 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13029789427200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249Coded : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 1))]
theorem atom0249Coded_decode : atom0249 = SparsePolynomial.decodeCubic 21 atom0249Coded := by decide +kernel
theorem atom0249Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) := by
  have h := atom0249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0250 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0250 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22027546931328 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250Coded : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 1))]
theorem atom0250Coded_decode : atom0250 = SparsePolynomial.decodeCubic 21 atom0250Coded := by decide +kernel
theorem atom0250Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded) := by
  have h := atom0250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0251 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0251 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20547763034400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251Coded : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 1))]
theorem atom0251Coded_decode : atom0251 = SparsePolynomial.decodeCubic 21 atom0251Coded := by decide +kernel
theorem atom0251Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) := by
  have h := atom0251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0252 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0252 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20553442761600 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252Coded : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 1))]
theorem atom0252Coded_decode : atom0252 = SparsePolynomial.decodeCubic 21 atom0252Coded := by decide +kernel
theorem atom0252Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded) := by
  have h := atom0252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0253 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0253 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21299316292800 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253Coded : CoefficientMerge.Poly := [(nat_lit 136, Int.ofNat (nat_lit 1))]
theorem atom0253Coded_decode : atom0253 = SparsePolynomial.decodeCubic 21 atom0253Coded := by decide +kernel
theorem atom0253Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) := by
  have h := atom0253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0254 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0254 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22058417203200 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254Coded : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 1))]
theorem atom0254Coded_decode : atom0254 = SparsePolynomial.decodeCubic 21 atom0254Coded := by decide +kernel
theorem atom0254Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) := by
  have h := atom0254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0255 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0255 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0255 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0255_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23415680646400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255Coded : CoefficientMerge.Poly := [(nat_lit 138, Int.ofNat (nat_lit 1))]
theorem atom0255Coded_decode : atom0255 = SparsePolynomial.decodeCubic 21 atom0255Coded := by decide +kernel
theorem atom0255Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded) := by
  have h := atom0255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block004 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000)), (nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000)), (nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400)), (nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400)), (nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600)), (nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248)), (nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616)), (nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
def block004_data_flat000 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800))]
theorem block004_data_flat000_step : block004_data_flat000 = (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) := by decide +kernel
theorem block004_data_flat000_original : block004_data_flat000 = (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) := by
  rw [block004_data_flat000_step]
def block004_data_flat001 : CoefficientMerge.Poly := [(nat_lit 38, Int.ofNat (nat_lit 1801017590400))]
theorem block004_data_flat001_step : block004_data_flat001 = (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded) := by decide +kernel
theorem block004_data_flat001_original : block004_data_flat001 = (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded) := by
  rw [block004_data_flat001_step]
def block004_data_flat002 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400))]
theorem block004_data_flat002_step : block004_data_flat002 = (CoefficientMerge.fastMerge block004_data_flat000 block004_data_flat001) := by decide +kernel
theorem block004_data_flat002_original : block004_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) := by
  rw [block004_data_flat002_step, block004_data_flat000_original, block004_data_flat001_original]
def block004_data_flat003 : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 787190140800))]
theorem block004_data_flat003_step : block004_data_flat003 = (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) := by decide +kernel
theorem block004_data_flat003_original : block004_data_flat003 = (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) := by
  rw [block004_data_flat003_step]
def block004_data_flat004 : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 420253545600))]
theorem block004_data_flat004_step : block004_data_flat004 = (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) := by decide +kernel
theorem block004_data_flat004_original : block004_data_flat004 = (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) := by
  rw [block004_data_flat004_step]
def block004_data_flat005 : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 7838074944000))]
theorem block004_data_flat005_step : block004_data_flat005 = (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded) := by decide +kernel
theorem block004_data_flat005_original : block004_data_flat005 = (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded) := by
  rw [block004_data_flat005_step]
def block004_data_flat006 : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000))]
theorem block004_data_flat006_step : block004_data_flat006 = (CoefficientMerge.fastMerge block004_data_flat004 block004_data_flat005) := by decide +kernel
theorem block004_data_flat006_original : block004_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)) := by
  rw [block004_data_flat006_step, block004_data_flat004_original, block004_data_flat005_original]
def block004_data_flat007 : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000))]
theorem block004_data_flat007_step : block004_data_flat007 = (CoefficientMerge.fastMerge block004_data_flat003 block004_data_flat006) := by decide +kernel
theorem block004_data_flat007_original : block004_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded))) := by
  rw [block004_data_flat007_step, block004_data_flat003_original, block004_data_flat006_original]
def block004_data_flat008 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000))]
theorem block004_data_flat008_step : block004_data_flat008 = (CoefficientMerge.fastMerge block004_data_flat002 block004_data_flat007) := by decide +kernel
theorem block004_data_flat008_original : block004_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) := by
  rw [block004_data_flat008_step, block004_data_flat002_original, block004_data_flat007_original]
def block004_data_flat009 : CoefficientMerge.Poly := [(nat_lit 45, Int.ofNat (nat_lit 16012481587200))]
theorem block004_data_flat009_step : block004_data_flat009 = (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) := by decide +kernel
theorem block004_data_flat009_original : block004_data_flat009 = (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) := by
  rw [block004_data_flat009_step]
def block004_data_flat010 : CoefficientMerge.Poly := [(nat_lit 46, Int.ofNat (nat_lit 16348813286400))]
theorem block004_data_flat010_step : block004_data_flat010 = (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded) := by decide +kernel
theorem block004_data_flat010_original : block004_data_flat010 = (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded) := by
  rw [block004_data_flat010_step]
def block004_data_flat011 : CoefficientMerge.Poly := [(nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400))]
theorem block004_data_flat011_step : block004_data_flat011 = (CoefficientMerge.fastMerge block004_data_flat009 block004_data_flat010) := by decide +kernel
theorem block004_data_flat011_original : block004_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) := by
  rw [block004_data_flat011_step, block004_data_flat009_original, block004_data_flat010_original]
def block004_data_flat012 : CoefficientMerge.Poly := [(nat_lit 47, Int.ofNat (nat_lit 16685144985600))]
theorem block004_data_flat012_step : block004_data_flat012 = (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) := by decide +kernel
theorem block004_data_flat012_original : block004_data_flat012 = (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) := by
  rw [block004_data_flat012_step]
def block004_data_flat013 : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 17021476684800))]
theorem block004_data_flat013_step : block004_data_flat013 = (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) := by decide +kernel
theorem block004_data_flat013_original : block004_data_flat013 = (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) := by
  rw [block004_data_flat013_step]
def block004_data_flat014 : CoefficientMerge.Poly := [(nat_lit 49, Int.ofNat (nat_lit 17357808384000))]
theorem block004_data_flat014_step : block004_data_flat014 = (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded) := by decide +kernel
theorem block004_data_flat014_original : block004_data_flat014 = (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded) := by
  rw [block004_data_flat014_step]
def block004_data_flat015 : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000))]
theorem block004_data_flat015_step : block004_data_flat015 = (CoefficientMerge.fastMerge block004_data_flat013 block004_data_flat014) := by decide +kernel
theorem block004_data_flat015_original : block004_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded)) := by
  rw [block004_data_flat015_step, block004_data_flat013_original, block004_data_flat014_original]
def block004_data_flat016 : CoefficientMerge.Poly := [(nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000))]
theorem block004_data_flat016_step : block004_data_flat016 = (CoefficientMerge.fastMerge block004_data_flat012 block004_data_flat015) := by decide +kernel
theorem block004_data_flat016_original : block004_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))) := by
  rw [block004_data_flat016_step, block004_data_flat012_original, block004_data_flat015_original]
def block004_data_flat017 : CoefficientMerge.Poly := [(nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000))]
theorem block004_data_flat017_step : block004_data_flat017 = (CoefficientMerge.fastMerge block004_data_flat011 block004_data_flat016) := by decide +kernel
theorem block004_data_flat017_original : block004_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded)))) := by
  rw [block004_data_flat017_step, block004_data_flat011_original, block004_data_flat016_original]
def block004_data_flat018 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000))]
theorem block004_data_flat018_step : block004_data_flat018 = (CoefficientMerge.fastMerge block004_data_flat008 block004_data_flat017) := by decide +kernel
theorem block004_data_flat018_original : block004_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) := by
  rw [block004_data_flat018_step, block004_data_flat008_original, block004_data_flat017_original]
def block004_data_flat019 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 17694140083200))]
theorem block004_data_flat019_step : block004_data_flat019 = (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) := by decide +kernel
theorem block004_data_flat019_original : block004_data_flat019 = (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) := by
  rw [block004_data_flat019_step]
def block004_data_flat020 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 18030471782400))]
theorem block004_data_flat020_step : block004_data_flat020 = (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded) := by decide +kernel
theorem block004_data_flat020_original : block004_data_flat020 = (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded) := by
  rw [block004_data_flat020_step]
def block004_data_flat021 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400))]
theorem block004_data_flat021_step : block004_data_flat021 = (CoefficientMerge.fastMerge block004_data_flat019 block004_data_flat020) := by decide +kernel
theorem block004_data_flat021_original : block004_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) := by
  rw [block004_data_flat021_step, block004_data_flat019_original, block004_data_flat020_original]
def block004_data_flat022 : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 18366803481600))]
theorem block004_data_flat022_step : block004_data_flat022 = (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) := by decide +kernel
theorem block004_data_flat022_original : block004_data_flat022 = (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) := by
  rw [block004_data_flat022_step]
def block004_data_flat023 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 18703135180800))]
theorem block004_data_flat023_step : block004_data_flat023 = (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) := by decide +kernel
theorem block004_data_flat023_original : block004_data_flat023 = (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) := by
  rw [block004_data_flat023_step]
def block004_data_flat024 : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 19039466880000))]
theorem block004_data_flat024_step : block004_data_flat024 = (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded) := by decide +kernel
theorem block004_data_flat024_original : block004_data_flat024 = (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded) := by
  rw [block004_data_flat024_step]
def block004_data_flat025 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000))]
theorem block004_data_flat025_step : block004_data_flat025 = (CoefficientMerge.fastMerge block004_data_flat023 block004_data_flat024) := by decide +kernel
theorem block004_data_flat025_original : block004_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)) := by
  rw [block004_data_flat025_step, block004_data_flat023_original, block004_data_flat024_original]
def block004_data_flat026 : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000))]
theorem block004_data_flat026_step : block004_data_flat026 = (CoefficientMerge.fastMerge block004_data_flat022 block004_data_flat025) := by decide +kernel
theorem block004_data_flat026_original : block004_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded))) := by
  rw [block004_data_flat026_step, block004_data_flat022_original, block004_data_flat025_original]
def block004_data_flat027 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000))]
theorem block004_data_flat027_step : block004_data_flat027 = (CoefficientMerge.fastMerge block004_data_flat021 block004_data_flat026) := by decide +kernel
theorem block004_data_flat027_original : block004_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) := by
  rw [block004_data_flat027_step, block004_data_flat021_original, block004_data_flat026_original]
def block004_data_flat028 : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 19375798579200))]
theorem block004_data_flat028_step : block004_data_flat028 = (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) := by decide +kernel
theorem block004_data_flat028_original : block004_data_flat028 = (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) := by
  rw [block004_data_flat028_step]
def block004_data_flat029 : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 19712130278400))]
theorem block004_data_flat029_step : block004_data_flat029 = (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded) := by decide +kernel
theorem block004_data_flat029_original : block004_data_flat029 = (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded) := by
  rw [block004_data_flat029_step]
def block004_data_flat030 : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400))]
theorem block004_data_flat030_step : block004_data_flat030 = (CoefficientMerge.fastMerge block004_data_flat028 block004_data_flat029) := by decide +kernel
theorem block004_data_flat030_original : block004_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) := by
  rw [block004_data_flat030_step, block004_data_flat028_original, block004_data_flat029_original]
def block004_data_flat031 : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 22980733171200))]
theorem block004_data_flat031_step : block004_data_flat031 = (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) := by decide +kernel
theorem block004_data_flat031_original : block004_data_flat031 = (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) := by
  rw [block004_data_flat031_step]
def block004_data_flat032 : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 13269638592000))]
theorem block004_data_flat032_step : block004_data_flat032 = (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) := by decide +kernel
theorem block004_data_flat032_original : block004_data_flat032 = (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) := by
  rw [block004_data_flat032_step]
def block004_data_flat033 : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat033_step : block004_data_flat033 = (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded) := by decide +kernel
theorem block004_data_flat033_original : block004_data_flat033 = (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded) := by
  rw [block004_data_flat033_step]
def block004_data_flat034 : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat034_step : block004_data_flat034 = (CoefficientMerge.fastMerge block004_data_flat032 block004_data_flat033) := by decide +kernel
theorem block004_data_flat034_original : block004_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)) := by
  rw [block004_data_flat034_step, block004_data_flat032_original, block004_data_flat033_original]
def block004_data_flat035 : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat035_step : block004_data_flat035 = (CoefficientMerge.fastMerge block004_data_flat031 block004_data_flat034) := by decide +kernel
theorem block004_data_flat035_original : block004_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded))) := by
  rw [block004_data_flat035_step, block004_data_flat031_original, block004_data_flat034_original]
def block004_data_flat036 : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat036_step : block004_data_flat036 = (CoefficientMerge.fastMerge block004_data_flat030 block004_data_flat035) := by decide +kernel
theorem block004_data_flat036_original : block004_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))) := by
  rw [block004_data_flat036_step, block004_data_flat030_original, block004_data_flat035_original]
def block004_data_flat037 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat037_step : block004_data_flat037 = (CoefficientMerge.fastMerge block004_data_flat027 block004_data_flat036) := by decide +kernel
theorem block004_data_flat037_original : block004_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded))))) := by
  rw [block004_data_flat037_step, block004_data_flat027_original, block004_data_flat036_original]
def block004_data_flat038 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000)), (nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000))]
theorem block004_data_flat038_step : block004_data_flat038 = (CoefficientMerge.fastMerge block004_data_flat018 block004_data_flat037) := by decide +kernel
theorem block004_data_flat038_original : block004_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) := by
  rw [block004_data_flat038_step, block004_data_flat018_original, block004_data_flat037_original]
def block004_data_flat039 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1702920844800))]
theorem block004_data_flat039_step : block004_data_flat039 = (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) := by decide +kernel
theorem block004_data_flat039_original : block004_data_flat039 = (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) := by
  rw [block004_data_flat039_step]
def block004_data_flat040 : CoefficientMerge.Poly := [(nat_lit 61, Int.ofNat (nat_lit 2888296790400))]
theorem block004_data_flat040_step : block004_data_flat040 = (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded) := by decide +kernel
theorem block004_data_flat040_original : block004_data_flat040 = (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded) := by
  rw [block004_data_flat040_step]
def block004_data_flat041 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400))]
theorem block004_data_flat041_step : block004_data_flat041 = (CoefficientMerge.fastMerge block004_data_flat039 block004_data_flat040) := by decide +kernel
theorem block004_data_flat041_original : block004_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) := by
  rw [block004_data_flat041_step, block004_data_flat039_original, block004_data_flat040_original]
def block004_data_flat042 : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 7747226726400))]
theorem block004_data_flat042_step : block004_data_flat042 = (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) := by decide +kernel
theorem block004_data_flat042_original : block004_data_flat042 = (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) := by
  rw [block004_data_flat042_step]
def block004_data_flat043 : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 15998951001600))]
theorem block004_data_flat043_step : block004_data_flat043 = (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) := by decide +kernel
theorem block004_data_flat043_original : block004_data_flat043 = (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) := by
  rw [block004_data_flat043_step]
def block004_data_flat044 : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 16503448550400))]
theorem block004_data_flat044_step : block004_data_flat044 = (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded) := by decide +kernel
theorem block004_data_flat044_original : block004_data_flat044 = (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded) := by
  rw [block004_data_flat044_step]
def block004_data_flat045 : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400))]
theorem block004_data_flat045_step : block004_data_flat045 = (CoefficientMerge.fastMerge block004_data_flat043 block004_data_flat044) := by decide +kernel
theorem block004_data_flat045_original : block004_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)) := by
  rw [block004_data_flat045_step, block004_data_flat043_original, block004_data_flat044_original]
def block004_data_flat046 : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400))]
theorem block004_data_flat046_step : block004_data_flat046 = (CoefficientMerge.fastMerge block004_data_flat042 block004_data_flat045) := by decide +kernel
theorem block004_data_flat046_original : block004_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded))) := by
  rw [block004_data_flat046_step, block004_data_flat042_original, block004_data_flat045_original]
def block004_data_flat047 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400))]
theorem block004_data_flat047_step : block004_data_flat047 = (CoefficientMerge.fastMerge block004_data_flat041 block004_data_flat046) := by decide +kernel
theorem block004_data_flat047_original : block004_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) := by
  rw [block004_data_flat047_step, block004_data_flat041_original, block004_data_flat046_original]
def block004_data_flat048 : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 17007946099200))]
theorem block004_data_flat048_step : block004_data_flat048 = (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) := by decide +kernel
theorem block004_data_flat048_original : block004_data_flat048 = (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) := by
  rw [block004_data_flat048_step]
def block004_data_flat049 : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 17512443648000))]
theorem block004_data_flat049_step : block004_data_flat049 = (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded) := by decide +kernel
theorem block004_data_flat049_original : block004_data_flat049 = (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded) := by
  rw [block004_data_flat049_step]
def block004_data_flat050 : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000))]
theorem block004_data_flat050_step : block004_data_flat050 = (CoefficientMerge.fastMerge block004_data_flat048 block004_data_flat049) := by decide +kernel
theorem block004_data_flat050_original : block004_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) := by
  rw [block004_data_flat050_step, block004_data_flat048_original, block004_data_flat049_original]
def block004_data_flat051 : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 18016941196800))]
theorem block004_data_flat051_step : block004_data_flat051 = (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) := by decide +kernel
theorem block004_data_flat051_original : block004_data_flat051 = (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) := by
  rw [block004_data_flat051_step]
def block004_data_flat052 : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 18521438745600))]
theorem block004_data_flat052_step : block004_data_flat052 = (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) := by decide +kernel
theorem block004_data_flat052_original : block004_data_flat052 = (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) := by
  rw [block004_data_flat052_step]
def block004_data_flat053 : CoefficientMerge.Poly := [(nat_lit 73, Int.ofNat (nat_lit 19025936294400))]
theorem block004_data_flat053_step : block004_data_flat053 = (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded) := by decide +kernel
theorem block004_data_flat053_original : block004_data_flat053 = (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded) := by
  rw [block004_data_flat053_step]
def block004_data_flat054 : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400))]
theorem block004_data_flat054_step : block004_data_flat054 = (CoefficientMerge.fastMerge block004_data_flat052 block004_data_flat053) := by decide +kernel
theorem block004_data_flat054_original : block004_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded)) := by
  rw [block004_data_flat054_step, block004_data_flat052_original, block004_data_flat053_original]
def block004_data_flat055 : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400))]
theorem block004_data_flat055_step : block004_data_flat055 = (CoefficientMerge.fastMerge block004_data_flat051 block004_data_flat054) := by decide +kernel
theorem block004_data_flat055_original : block004_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))) := by
  rw [block004_data_flat055_step, block004_data_flat051_original, block004_data_flat054_original]
def block004_data_flat056 : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400))]
theorem block004_data_flat056_step : block004_data_flat056 = (CoefficientMerge.fastMerge block004_data_flat050 block004_data_flat055) := by decide +kernel
theorem block004_data_flat056_original : block004_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded)))) := by
  rw [block004_data_flat056_step, block004_data_flat050_original, block004_data_flat055_original]
def block004_data_flat057 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400))]
theorem block004_data_flat057_step : block004_data_flat057 = (CoefficientMerge.fastMerge block004_data_flat047 block004_data_flat056) := by decide +kernel
theorem block004_data_flat057_original : block004_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) := by
  rw [block004_data_flat057_step, block004_data_flat047_original, block004_data_flat056_original]
def block004_data_flat058 : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 19530433843200))]
theorem block004_data_flat058_step : block004_data_flat058 = (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) := by decide +kernel
theorem block004_data_flat058_original : block004_data_flat058 = (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) := by
  rw [block004_data_flat058_step]
def block004_data_flat059 : CoefficientMerge.Poly := [(nat_lit 75, Int.ofNat (nat_lit 20034931392000))]
theorem block004_data_flat059_step : block004_data_flat059 = (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded) := by decide +kernel
theorem block004_data_flat059_original : block004_data_flat059 = (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded) := by
  rw [block004_data_flat059_step]
def block004_data_flat060 : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000))]
theorem block004_data_flat060_step : block004_data_flat060 = (CoefficientMerge.fastMerge block004_data_flat058 block004_data_flat059) := by decide +kernel
theorem block004_data_flat060_original : block004_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) := by
  rw [block004_data_flat060_step, block004_data_flat058_original, block004_data_flat059_original]
def block004_data_flat061 : CoefficientMerge.Poly := [(nat_lit 76, Int.ofNat (nat_lit 20539428940800))]
theorem block004_data_flat061_step : block004_data_flat061 = (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) := by decide +kernel
theorem block004_data_flat061_original : block004_data_flat061 = (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) := by
  rw [block004_data_flat061_step]
def block004_data_flat062 : CoefficientMerge.Poly := [(nat_lit 77, Int.ofNat (nat_lit 21043926489600))]
theorem block004_data_flat062_step : block004_data_flat062 = (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) := by decide +kernel
theorem block004_data_flat062_original : block004_data_flat062 = (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) := by
  rw [block004_data_flat062_step]
def block004_data_flat063 : CoefficientMerge.Poly := [(nat_lit 78, Int.ofNat (nat_lit 24373900252800))]
theorem block004_data_flat063_step : block004_data_flat063 = (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded) := by decide +kernel
theorem block004_data_flat063_original : block004_data_flat063 = (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded) := by
  rw [block004_data_flat063_step]
def block004_data_flat064 : CoefficientMerge.Poly := [(nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800))]
theorem block004_data_flat064_step : block004_data_flat064 = (CoefficientMerge.fastMerge block004_data_flat062 block004_data_flat063) := by decide +kernel
theorem block004_data_flat064_original : block004_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)) := by
  rw [block004_data_flat064_step, block004_data_flat062_original, block004_data_flat063_original]
def block004_data_flat065 : CoefficientMerge.Poly := [(nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800))]
theorem block004_data_flat065_step : block004_data_flat065 = (CoefficientMerge.fastMerge block004_data_flat061 block004_data_flat064) := by decide +kernel
theorem block004_data_flat065_original : block004_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded))) := by
  rw [block004_data_flat065_step, block004_data_flat061_original, block004_data_flat064_original]
def block004_data_flat066 : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800))]
theorem block004_data_flat066_step : block004_data_flat066 = (CoefficientMerge.fastMerge block004_data_flat060 block004_data_flat065) := by decide +kernel
theorem block004_data_flat066_original : block004_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) := by
  rw [block004_data_flat066_step, block004_data_flat060_original, block004_data_flat065_original]
def block004_data_flat067 : CoefficientMerge.Poly := [(nat_lit 79, Int.ofNat (nat_lit 15288112022400))]
theorem block004_data_flat067_step : block004_data_flat067 = (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) := by decide +kernel
theorem block004_data_flat067_original : block004_data_flat067 = (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) := by
  rw [block004_data_flat067_step]
def block004_data_flat068 : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 11985579849600))]
theorem block004_data_flat068_step : block004_data_flat068 = (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded) := by decide +kernel
theorem block004_data_flat068_original : block004_data_flat068 = (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded) := by
  rw [block004_data_flat068_step]
def block004_data_flat069 : CoefficientMerge.Poly := [(nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600))]
theorem block004_data_flat069_step : block004_data_flat069 = (CoefficientMerge.fastMerge block004_data_flat067 block004_data_flat068) := by decide +kernel
theorem block004_data_flat069_original : block004_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) := by
  rw [block004_data_flat069_step, block004_data_flat067_original, block004_data_flat068_original]
def block004_data_flat070 : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 3766818384000))]
theorem block004_data_flat070_step : block004_data_flat070 = (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) := by decide +kernel
theorem block004_data_flat070_original : block004_data_flat070 = (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) := by
  rw [block004_data_flat070_step]
def block004_data_flat071 : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 5075419305600))]
theorem block004_data_flat071_step : block004_data_flat071 = (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) := by decide +kernel
theorem block004_data_flat071_original : block004_data_flat071 = (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) := by
  rw [block004_data_flat071_step]
def block004_data_flat072 : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat072_step : block004_data_flat072 = (CoefficientMerge.scale (389970806400 : Int) atom0215Coded) := by decide +kernel
theorem block004_data_flat072_original : block004_data_flat072 = (CoefficientMerge.scale (389970806400 : Int) atom0215Coded) := by
  rw [block004_data_flat072_step]
def block004_data_flat073 : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat073_step : block004_data_flat073 = (CoefficientMerge.fastMerge block004_data_flat071 block004_data_flat072) := by decide +kernel
theorem block004_data_flat073_original : block004_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded)) := by
  rw [block004_data_flat073_step, block004_data_flat071_original, block004_data_flat072_original]
def block004_data_flat074 : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat074_step : block004_data_flat074 = (CoefficientMerge.fastMerge block004_data_flat070 block004_data_flat073) := by decide +kernel
theorem block004_data_flat074_original : block004_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))) := by
  rw [block004_data_flat074_step, block004_data_flat070_original, block004_data_flat073_original]
def block004_data_flat075 : CoefficientMerge.Poly := [(nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat075_step : block004_data_flat075 = (CoefficientMerge.fastMerge block004_data_flat069 block004_data_flat074) := by decide +kernel
theorem block004_data_flat075_original : block004_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded)))) := by
  rw [block004_data_flat075_step, block004_data_flat069_original, block004_data_flat074_original]
def block004_data_flat076 : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat076_step : block004_data_flat076 = (CoefficientMerge.fastMerge block004_data_flat066 block004_data_flat075) := by decide +kernel
theorem block004_data_flat076_original : block004_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))) := by
  rw [block004_data_flat076_step, block004_data_flat066_original, block004_data_flat075_original]
def block004_data_flat077 : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400)), (nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat077_step : block004_data_flat077 = (CoefficientMerge.fastMerge block004_data_flat057 block004_data_flat076) := by decide +kernel
theorem block004_data_flat077_original : block004_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded)))))) := by
  rw [block004_data_flat077_step, block004_data_flat057_original, block004_data_flat076_original]
def block004_data_flat078 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000)), (nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000)), (nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400)), (nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400))]
theorem block004_data_flat078_step : block004_data_flat078 = (CoefficientMerge.fastMerge block004_data_flat038 block004_data_flat077) := by decide +kernel
theorem block004_data_flat078_original : block004_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))))) := by
  rw [block004_data_flat078_step, block004_data_flat038_original, block004_data_flat077_original]
def block004_data_flat079 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000))]
theorem block004_data_flat079_step : block004_data_flat079 = (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) := by decide +kernel
theorem block004_data_flat079_original : block004_data_flat079 = (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) := by
  rw [block004_data_flat079_step]
def block004_data_flat080 : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 16329426810624))]
theorem block004_data_flat080_step : block004_data_flat080 = (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded) := by decide +kernel
theorem block004_data_flat080_original : block004_data_flat080 = (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded) := by
  rw [block004_data_flat080_step]
def block004_data_flat081 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624))]
theorem block004_data_flat081_step : block004_data_flat081 = (CoefficientMerge.fastMerge block004_data_flat079 block004_data_flat080) := by decide +kernel
theorem block004_data_flat081_original : block004_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) := by
  rw [block004_data_flat081_step, block004_data_flat079_original, block004_data_flat080_original]
def block004_data_flat082 : CoefficientMerge.Poly := [(nat_lit 90, Int.ofNat (nat_lit 16994415513600))]
theorem block004_data_flat082_step : block004_data_flat082 = (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) := by decide +kernel
theorem block004_data_flat082_original : block004_data_flat082 = (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) := by
  rw [block004_data_flat082_step]
def block004_data_flat083 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 17667078912000))]
theorem block004_data_flat083_step : block004_data_flat083 = (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) := by decide +kernel
theorem block004_data_flat083_original : block004_data_flat083 = (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) := by
  rw [block004_data_flat083_step]
def block004_data_flat084 : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 18339742310400))]
theorem block004_data_flat084_step : block004_data_flat084 = (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded) := by decide +kernel
theorem block004_data_flat084_original : block004_data_flat084 = (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded) := by
  rw [block004_data_flat084_step]
def block004_data_flat085 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400))]
theorem block004_data_flat085_step : block004_data_flat085 = (CoefficientMerge.fastMerge block004_data_flat083 block004_data_flat084) := by decide +kernel
theorem block004_data_flat085_original : block004_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)) := by
  rw [block004_data_flat085_step, block004_data_flat083_original, block004_data_flat084_original]
def block004_data_flat086 : CoefficientMerge.Poly := [(nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400))]
theorem block004_data_flat086_step : block004_data_flat086 = (CoefficientMerge.fastMerge block004_data_flat082 block004_data_flat085) := by decide +kernel
theorem block004_data_flat086_original : block004_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded))) := by
  rw [block004_data_flat086_step, block004_data_flat082_original, block004_data_flat085_original]
def block004_data_flat087 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400))]
theorem block004_data_flat087_step : block004_data_flat087 = (CoefficientMerge.fastMerge block004_data_flat081 block004_data_flat086) := by decide +kernel
theorem block004_data_flat087_original : block004_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) := by
  rw [block004_data_flat087_step, block004_data_flat081_original, block004_data_flat086_original]
def block004_data_flat088 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 19012405708800))]
theorem block004_data_flat088_step : block004_data_flat088 = (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) := by decide +kernel
theorem block004_data_flat088_original : block004_data_flat088 = (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) := by
  rw [block004_data_flat088_step]
def block004_data_flat089 : CoefficientMerge.Poly := [(nat_lit 94, Int.ofNat (nat_lit 19685069107200))]
theorem block004_data_flat089_step : block004_data_flat089 = (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded) := by decide +kernel
theorem block004_data_flat089_original : block004_data_flat089 = (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded) := by
  rw [block004_data_flat089_step]
def block004_data_flat090 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200))]
theorem block004_data_flat090_step : block004_data_flat090 = (CoefficientMerge.fastMerge block004_data_flat088 block004_data_flat089) := by decide +kernel
theorem block004_data_flat090_original : block004_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) := by
  rw [block004_data_flat090_step, block004_data_flat088_original, block004_data_flat089_original]
def block004_data_flat091 : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 20357732505600))]
theorem block004_data_flat091_step : block004_data_flat091 = (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) := by decide +kernel
theorem block004_data_flat091_original : block004_data_flat091 = (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) := by
  rw [block004_data_flat091_step]
def block004_data_flat092 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 21233148865600))]
theorem block004_data_flat092_step : block004_data_flat092 = (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) := by decide +kernel
theorem block004_data_flat092_original : block004_data_flat092 = (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) := by
  rw [block004_data_flat092_step]
def block004_data_flat093 : CoefficientMerge.Poly := [(nat_lit 97, Int.ofNat (nat_lit 22067177025600))]
theorem block004_data_flat093_step : block004_data_flat093 = (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded) := by decide +kernel
theorem block004_data_flat093_original : block004_data_flat093 = (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded) := by
  rw [block004_data_flat093_step]
def block004_data_flat094 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600))]
theorem block004_data_flat094_step : block004_data_flat094 = (CoefficientMerge.fastMerge block004_data_flat092 block004_data_flat093) := by decide +kernel
theorem block004_data_flat094_original : block004_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded)) := by
  rw [block004_data_flat094_step, block004_data_flat092_original, block004_data_flat093_original]
def block004_data_flat095 : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600))]
theorem block004_data_flat095_step : block004_data_flat095 = (CoefficientMerge.fastMerge block004_data_flat091 block004_data_flat094) := by decide +kernel
theorem block004_data_flat095_original : block004_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))) := by
  rw [block004_data_flat095_step, block004_data_flat091_original, block004_data_flat094_original]
def block004_data_flat096 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600))]
theorem block004_data_flat096_step : block004_data_flat096 = (CoefficientMerge.fastMerge block004_data_flat090 block004_data_flat095) := by decide +kernel
theorem block004_data_flat096_original : block004_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded)))) := by
  rw [block004_data_flat096_step, block004_data_flat090_original, block004_data_flat095_original]
def block004_data_flat097 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600))]
theorem block004_data_flat097_step : block004_data_flat097 = (CoefficientMerge.fastMerge block004_data_flat087 block004_data_flat096) := by decide +kernel
theorem block004_data_flat097_original : block004_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) := by
  rw [block004_data_flat097_step, block004_data_flat087_original, block004_data_flat096_original]
def block004_data_flat098 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 22681852200000))]
theorem block004_data_flat098_step : block004_data_flat098 = (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) := by decide +kernel
theorem block004_data_flat098_original : block004_data_flat098 = (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) := by
  rw [block004_data_flat098_step]
def block004_data_flat099 : CoefficientMerge.Poly := [(nat_lit 99, Int.ofNat (nat_lit 25767067334400))]
theorem block004_data_flat099_step : block004_data_flat099 = (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded) := by decide +kernel
theorem block004_data_flat099_original : block004_data_flat099 = (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded) := by
  rw [block004_data_flat099_step]
def block004_data_flat100 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400))]
theorem block004_data_flat100_step : block004_data_flat100 = (CoefficientMerge.fastMerge block004_data_flat098 block004_data_flat099) := by decide +kernel
theorem block004_data_flat100_original : block004_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) := by
  rw [block004_data_flat100_step, block004_data_flat098_original, block004_data_flat099_original]
def block004_data_flat101 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 17557535532600))]
theorem block004_data_flat101_step : block004_data_flat101 = (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) := by decide +kernel
theorem block004_data_flat101_original : block004_data_flat101 = (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) := by
  rw [block004_data_flat101_step]
def block004_data_flat102 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 13074308755200))]
theorem block004_data_flat102_step : block004_data_flat102 = (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) := by decide +kernel
theorem block004_data_flat102_original : block004_data_flat102 = (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) := by
  rw [block004_data_flat102_step]
def block004_data_flat103 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 6011898921000))]
theorem block004_data_flat103_step : block004_data_flat103 = (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded) := by decide +kernel
theorem block004_data_flat103_original : block004_data_flat103 = (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded) := by
  rw [block004_data_flat103_step]
def block004_data_flat104 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000))]
theorem block004_data_flat104_step : block004_data_flat104 = (CoefficientMerge.fastMerge block004_data_flat102 block004_data_flat103) := by decide +kernel
theorem block004_data_flat104_original : block004_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)) := by
  rw [block004_data_flat104_step, block004_data_flat102_original, block004_data_flat103_original]
def block004_data_flat105 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000))]
theorem block004_data_flat105_step : block004_data_flat105 = (CoefficientMerge.fastMerge block004_data_flat101 block004_data_flat104) := by decide +kernel
theorem block004_data_flat105_original : block004_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded))) := by
  rw [block004_data_flat105_step, block004_data_flat101_original, block004_data_flat104_original]
def block004_data_flat106 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000))]
theorem block004_data_flat106_step : block004_data_flat106 = (CoefficientMerge.fastMerge block004_data_flat100 block004_data_flat105) := by decide +kernel
theorem block004_data_flat106_original : block004_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) := by
  rw [block004_data_flat106_step, block004_data_flat100_original, block004_data_flat105_original]
def block004_data_flat107 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 7268672867400))]
theorem block004_data_flat107_step : block004_data_flat107 = (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) := by decide +kernel
theorem block004_data_flat107_original : block004_data_flat107 = (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) := by
  rw [block004_data_flat107_step]
def block004_data_flat108 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 2531397393000))]
theorem block004_data_flat108_step : block004_data_flat108 = (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded) := by decide +kernel
theorem block004_data_flat108_original : block004_data_flat108 = (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded) := by
  rw [block004_data_flat108_step]
def block004_data_flat109 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000))]
theorem block004_data_flat109_step : block004_data_flat109 = (CoefficientMerge.fastMerge block004_data_flat107 block004_data_flat108) := by decide +kernel
theorem block004_data_flat109_original : block004_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) := by
  rw [block004_data_flat109_step, block004_data_flat107_original, block004_data_flat108_original]
def block004_data_flat110 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 10430034421248))]
theorem block004_data_flat110_step : block004_data_flat110 = (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) := by decide +kernel
theorem block004_data_flat110_original : block004_data_flat110 = (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) := by
  rw [block004_data_flat110_step]
def block004_data_flat111 : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 18863725537728))]
theorem block004_data_flat111_step : block004_data_flat111 = (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) := by decide +kernel
theorem block004_data_flat111_original : block004_data_flat111 = (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) := by
  rw [block004_data_flat111_step]
def block004_data_flat112 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat112_step : block004_data_flat112 = (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded) := by decide +kernel
theorem block004_data_flat112_original : block004_data_flat112 = (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded) := by
  rw [block004_data_flat112_step]
def block004_data_flat113 : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat113_step : block004_data_flat113 = (CoefficientMerge.fastMerge block004_data_flat111 block004_data_flat112) := by decide +kernel
theorem block004_data_flat113_original : block004_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)) := by
  rw [block004_data_flat113_step, block004_data_flat111_original, block004_data_flat112_original]
def block004_data_flat114 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat114_step : block004_data_flat114 = (CoefficientMerge.fastMerge block004_data_flat110 block004_data_flat113) := by decide +kernel
theorem block004_data_flat114_original : block004_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded))) := by
  rw [block004_data_flat114_step, block004_data_flat110_original, block004_data_flat113_original]
def block004_data_flat115 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat115_step : block004_data_flat115 = (CoefficientMerge.fastMerge block004_data_flat109 block004_data_flat114) := by decide +kernel
theorem block004_data_flat115_original : block004_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))) := by
  rw [block004_data_flat115_step, block004_data_flat109_original, block004_data_flat114_original]
def block004_data_flat116 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat116_step : block004_data_flat116 = (CoefficientMerge.fastMerge block004_data_flat106 block004_data_flat115) := by decide +kernel
theorem block004_data_flat116_original : block004_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded))))) := by
  rw [block004_data_flat116_step, block004_data_flat106_original, block004_data_flat115_original]
def block004_data_flat117 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600)), (nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248))]
theorem block004_data_flat117_step : block004_data_flat117 = (CoefficientMerge.fastMerge block004_data_flat097 block004_data_flat116) := by decide +kernel
theorem block004_data_flat117_original : block004_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) := by
  rw [block004_data_flat117_step, block004_data_flat097_original, block004_data_flat116_original]
def block004_data_flat118 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 18662543424000))]
theorem block004_data_flat118_step : block004_data_flat118 = (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) := by decide +kernel
theorem block004_data_flat118_original : block004_data_flat118 = (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) := by
  rw [block004_data_flat118_step]
def block004_data_flat119 : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 19685793960000))]
theorem block004_data_flat119_step : block004_data_flat119 = (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded) := by decide +kernel
theorem block004_data_flat119_original : block004_data_flat119 = (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded) := by
  rw [block004_data_flat119_step]
def block004_data_flat120 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000))]
theorem block004_data_flat120_step : block004_data_flat120 = (CoefficientMerge.fastMerge block004_data_flat118 block004_data_flat119) := by decide +kernel
theorem block004_data_flat120_original : block004_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) := by
  rw [block004_data_flat120_step, block004_data_flat118_original, block004_data_flat119_original]
def block004_data_flat121 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 20344201920000))]
theorem block004_data_flat121_step : block004_data_flat121 = (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) := by decide +kernel
theorem block004_data_flat121_original : block004_data_flat121 = (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) := by
  rw [block004_data_flat121_step]
def block004_data_flat122 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 21185031168000))]
theorem block004_data_flat122_step : block004_data_flat122 = (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) := by decide +kernel
theorem block004_data_flat122_original : block004_data_flat122 = (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) := by
  rw [block004_data_flat122_step]
def block004_data_flat123 : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 22373100702400))]
theorem block004_data_flat123_step : block004_data_flat123 = (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded) := by decide +kernel
theorem block004_data_flat123_original : block004_data_flat123 = (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded) := by
  rw [block004_data_flat123_step]
def block004_data_flat124 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400))]
theorem block004_data_flat124_step : block004_data_flat124 = (CoefficientMerge.fastMerge block004_data_flat122 block004_data_flat123) := by decide +kernel
theorem block004_data_flat124_original : block004_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)) := by
  rw [block004_data_flat124_step, block004_data_flat122_original, block004_data_flat123_original]
def block004_data_flat125 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400))]
theorem block004_data_flat125_step : block004_data_flat125 = (CoefficientMerge.fastMerge block004_data_flat121 block004_data_flat124) := by decide +kernel
theorem block004_data_flat125_original : block004_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded))) := by
  rw [block004_data_flat125_step, block004_data_flat121_original, block004_data_flat124_original]
def block004_data_flat126 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400))]
theorem block004_data_flat126_step : block004_data_flat126 = (CoefficientMerge.fastMerge block004_data_flat120 block004_data_flat125) := by decide +kernel
theorem block004_data_flat126_original : block004_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) := by
  rw [block004_data_flat126_step, block004_data_flat120_original, block004_data_flat125_original]
def block004_data_flat127 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 23206404009600))]
theorem block004_data_flat127_step : block004_data_flat127 = (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) := by decide +kernel
theorem block004_data_flat127_original : block004_data_flat127 = (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) := by
  rw [block004_data_flat127_step]
def block004_data_flat128 : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 23885832700800))]
theorem block004_data_flat128_step : block004_data_flat128 = (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded) := by decide +kernel
theorem block004_data_flat128_original : block004_data_flat128 = (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded) := by
  rw [block004_data_flat128_step]
def block004_data_flat129 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800))]
theorem block004_data_flat129_step : block004_data_flat129 = (CoefficientMerge.fastMerge block004_data_flat127 block004_data_flat128) := by decide +kernel
theorem block004_data_flat129_original : block004_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) := by
  rw [block004_data_flat129_step, block004_data_flat127_original, block004_data_flat128_original]
def block004_data_flat130 : CoefficientMerge.Poly := [(nat_lit 120, Int.ofNat (nat_lit 27533078906688))]
theorem block004_data_flat130_step : block004_data_flat130 = (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) := by decide +kernel
theorem block004_data_flat130_original : block004_data_flat130 = (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) := by
  rw [block004_data_flat130_step]
def block004_data_flat131 : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 19930254363648))]
theorem block004_data_flat131_step : block004_data_flat131 = (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) := by decide +kernel
theorem block004_data_flat131_original : block004_data_flat131 = (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) := by
  rw [block004_data_flat131_step]
def block004_data_flat132 : CoefficientMerge.Poly := [(nat_lit 122, Int.ofNat (nat_lit 16772949095616))]
theorem block004_data_flat132_step : block004_data_flat132 = (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded) := by decide +kernel
theorem block004_data_flat132_original : block004_data_flat132 = (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded) := by
  rw [block004_data_flat132_step]
def block004_data_flat133 : CoefficientMerge.Poly := [(nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616))]
theorem block004_data_flat133_step : block004_data_flat133 = (CoefficientMerge.fastMerge block004_data_flat131 block004_data_flat132) := by decide +kernel
theorem block004_data_flat133_original : block004_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded)) := by
  rw [block004_data_flat133_step, block004_data_flat131_original, block004_data_flat132_original]
def block004_data_flat134 : CoefficientMerge.Poly := [(nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616))]
theorem block004_data_flat134_step : block004_data_flat134 = (CoefficientMerge.fastMerge block004_data_flat130 block004_data_flat133) := by decide +kernel
theorem block004_data_flat134_original : block004_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))) := by
  rw [block004_data_flat134_step, block004_data_flat130_original, block004_data_flat133_original]
def block004_data_flat135 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616))]
theorem block004_data_flat135_step : block004_data_flat135 = (CoefficientMerge.fastMerge block004_data_flat129 block004_data_flat134) := by decide +kernel
theorem block004_data_flat135_original : block004_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded)))) := by
  rw [block004_data_flat135_step, block004_data_flat129_original, block004_data_flat134_original]
def block004_data_flat136 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616))]
theorem block004_data_flat136_step : block004_data_flat136 = (CoefficientMerge.fastMerge block004_data_flat126 block004_data_flat135) := by decide +kernel
theorem block004_data_flat136_original : block004_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) := by
  rw [block004_data_flat136_step, block004_data_flat126_original, block004_data_flat135_original]
def block004_data_flat137 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 10592587378944))]
theorem block004_data_flat137_step : block004_data_flat137 = (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) := by decide +kernel
theorem block004_data_flat137_original : block004_data_flat137 = (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) := by
  rw [block004_data_flat137_step]
def block004_data_flat138 : CoefficientMerge.Poly := [(nat_lit 124, Int.ofNat (nat_lit 11062689626880))]
theorem block004_data_flat138_step : block004_data_flat138 = (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded) := by decide +kernel
theorem block004_data_flat138_original : block004_data_flat138 = (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded) := by
  rw [block004_data_flat138_step]
def block004_data_flat139 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880))]
theorem block004_data_flat139_step : block004_data_flat139 = (CoefficientMerge.fastMerge block004_data_flat137 block004_data_flat138) := by decide +kernel
theorem block004_data_flat139_original : block004_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) := by
  rw [block004_data_flat139_step, block004_data_flat137_original, block004_data_flat138_original]
def block004_data_flat140 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 7775809398144))]
theorem block004_data_flat140_step : block004_data_flat140 = (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) := by decide +kernel
theorem block004_data_flat140_original : block004_data_flat140 = (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) := by
  rw [block004_data_flat140_step]
def block004_data_flat141 : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 13029789427200))]
theorem block004_data_flat141_step : block004_data_flat141 = (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) := by decide +kernel
theorem block004_data_flat141_original : block004_data_flat141 = (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) := by
  rw [block004_data_flat141_step]
def block004_data_flat142 : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 22027546931328))]
theorem block004_data_flat142_step : block004_data_flat142 = (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded) := by decide +kernel
theorem block004_data_flat142_original : block004_data_flat142 = (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded) := by
  rw [block004_data_flat142_step]
def block004_data_flat143 : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328))]
theorem block004_data_flat143_step : block004_data_flat143 = (CoefficientMerge.fastMerge block004_data_flat141 block004_data_flat142) := by decide +kernel
theorem block004_data_flat143_original : block004_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)) := by
  rw [block004_data_flat143_step, block004_data_flat141_original, block004_data_flat142_original]
def block004_data_flat144 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328))]
theorem block004_data_flat144_step : block004_data_flat144 = (CoefficientMerge.fastMerge block004_data_flat140 block004_data_flat143) := by decide +kernel
theorem block004_data_flat144_original : block004_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded))) := by
  rw [block004_data_flat144_step, block004_data_flat140_original, block004_data_flat143_original]
def block004_data_flat145 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328))]
theorem block004_data_flat145_step : block004_data_flat145 = (CoefficientMerge.fastMerge block004_data_flat139 block004_data_flat144) := by decide +kernel
theorem block004_data_flat145_original : block004_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) := by
  rw [block004_data_flat145_step, block004_data_flat139_original, block004_data_flat144_original]
def block004_data_flat146 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 20547763034400))]
theorem block004_data_flat146_step : block004_data_flat146 = (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) := by decide +kernel
theorem block004_data_flat146_original : block004_data_flat146 = (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) := by
  rw [block004_data_flat146_step]
def block004_data_flat147 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 20553442761600))]
theorem block004_data_flat147_step : block004_data_flat147 = (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded) := by decide +kernel
theorem block004_data_flat147_original : block004_data_flat147 = (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded) := by
  rw [block004_data_flat147_step]
def block004_data_flat148 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600))]
theorem block004_data_flat148_step : block004_data_flat148 = (CoefficientMerge.fastMerge block004_data_flat146 block004_data_flat147) := by decide +kernel
theorem block004_data_flat148_original : block004_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) := by
  rw [block004_data_flat148_step, block004_data_flat146_original, block004_data_flat147_original]
def block004_data_flat149 : CoefficientMerge.Poly := [(nat_lit 136, Int.ofNat (nat_lit 21299316292800))]
theorem block004_data_flat149_step : block004_data_flat149 = (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) := by decide +kernel
theorem block004_data_flat149_original : block004_data_flat149 = (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) := by
  rw [block004_data_flat149_step]
def block004_data_flat150 : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 22058417203200))]
theorem block004_data_flat150_step : block004_data_flat150 = (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) := by decide +kernel
theorem block004_data_flat150_original : block004_data_flat150 = (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) := by
  rw [block004_data_flat150_step]
def block004_data_flat151 : CoefficientMerge.Poly := [(nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat151_step : block004_data_flat151 = (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded) := by decide +kernel
theorem block004_data_flat151_original : block004_data_flat151 = (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded) := by
  rw [block004_data_flat151_step]
def block004_data_flat152 : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat152_step : block004_data_flat152 = (CoefficientMerge.fastMerge block004_data_flat150 block004_data_flat151) := by decide +kernel
theorem block004_data_flat152_original : block004_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)) := by
  rw [block004_data_flat152_step, block004_data_flat150_original, block004_data_flat151_original]
def block004_data_flat153 : CoefficientMerge.Poly := [(nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat153_step : block004_data_flat153 = (CoefficientMerge.fastMerge block004_data_flat149 block004_data_flat152) := by decide +kernel
theorem block004_data_flat153_original : block004_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded))) := by
  rw [block004_data_flat153_step, block004_data_flat149_original, block004_data_flat152_original]
def block004_data_flat154 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat154_step : block004_data_flat154 = (CoefficientMerge.fastMerge block004_data_flat148 block004_data_flat153) := by decide +kernel
theorem block004_data_flat154_original : block004_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)))) := by
  rw [block004_data_flat154_step, block004_data_flat148_original, block004_data_flat153_original]
def block004_data_flat155 : CoefficientMerge.Poly := [(nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat155_step : block004_data_flat155 = (CoefficientMerge.fastMerge block004_data_flat145 block004_data_flat154) := by decide +kernel
theorem block004_data_flat155_original : block004_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded))))) := by
  rw [block004_data_flat155_step, block004_data_flat145_original, block004_data_flat154_original]
def block004_data_flat156 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616)), (nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat156_step : block004_data_flat156 = (CoefficientMerge.fastMerge block004_data_flat136 block004_data_flat155) := by decide +kernel
theorem block004_data_flat156_original : block004_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)))))) := by
  rw [block004_data_flat156_step, block004_data_flat136_original, block004_data_flat155_original]
def block004_data_flat157 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600)), (nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248)), (nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616)), (nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat157_step : block004_data_flat157 = (CoefficientMerge.fastMerge block004_data_flat117 block004_data_flat156) := by decide +kernel
theorem block004_data_flat157_original : block004_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded))))))) := by
  rw [block004_data_flat157_step, block004_data_flat117_original, block004_data_flat156_original]
def block004_data_flat158 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000)), (nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000)), (nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400)), (nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400)), (nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600)), (nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248)), (nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616)), (nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat158_step : block004_data_flat158 = (CoefficientMerge.fastMerge block004_data_flat078 block004_data_flat157) := by decide +kernel
theorem block004_data_flat158_original : block004_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)))))))) := by
  rw [block004_data_flat158_step, block004_data_flat078_original, block004_data_flat157_original]
def block004_data_flat159 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 5302217692800)), (nat_lit 38, Int.ofNat (nat_lit 1801017590400)), (nat_lit 39, Int.ofNat (nat_lit 787190140800)), (nat_lit 40, Int.ofNat (nat_lit 420253545600)), (nat_lit 44, Int.ofNat (nat_lit 7838074944000)), (nat_lit 45, Int.ofNat (nat_lit 16012481587200)), (nat_lit 46, Int.ofNat (nat_lit 16348813286400)), (nat_lit 47, Int.ofNat (nat_lit 16685144985600)), (nat_lit 48, Int.ofNat (nat_lit 17021476684800)), (nat_lit 49, Int.ofNat (nat_lit 17357808384000)), (nat_lit 50, Int.ofNat (nat_lit 17694140083200)), (nat_lit 51, Int.ofNat (nat_lit 18030471782400)), (nat_lit 52, Int.ofNat (nat_lit 18366803481600)), (nat_lit 53, Int.ofNat (nat_lit 18703135180800)), (nat_lit 54, Int.ofNat (nat_lit 19039466880000)), (nat_lit 55, Int.ofNat (nat_lit 19375798579200)), (nat_lit 56, Int.ofNat (nat_lit 19712130278400)), (nat_lit 57, Int.ofNat (nat_lit 22980733171200)), (nat_lit 58, Int.ofNat (nat_lit 13269638592000)), (nat_lit 59, Int.ofNat (nat_lit 10896850944000)), (nat_lit 60, Int.ofNat (nat_lit 1702920844800)), (nat_lit 61, Int.ofNat (nat_lit 2888296790400)), (nat_lit 66, Int.ofNat (nat_lit 7747226726400)), (nat_lit 67, Int.ofNat (nat_lit 15998951001600)), (nat_lit 68, Int.ofNat (nat_lit 16503448550400)), (nat_lit 69, Int.ofNat (nat_lit 17007946099200)), (nat_lit 70, Int.ofNat (nat_lit 17512443648000)), (nat_lit 71, Int.ofNat (nat_lit 18016941196800)), (nat_lit 72, Int.ofNat (nat_lit 18521438745600)), (nat_lit 73, Int.ofNat (nat_lit 19025936294400)), (nat_lit 74, Int.ofNat (nat_lit 19530433843200)), (nat_lit 75, Int.ofNat (nat_lit 20034931392000)), (nat_lit 76, Int.ofNat (nat_lit 20539428940800)), (nat_lit 77, Int.ofNat (nat_lit 21043926489600)), (nat_lit 78, Int.ofNat (nat_lit 24373900252800)), (nat_lit 79, Int.ofNat (nat_lit 15288112022400)), (nat_lit 80, Int.ofNat (nat_lit 11985579849600)), (nat_lit 81, Int.ofNat (nat_lit 3766818384000)), (nat_lit 82, Int.ofNat (nat_lit 5075419305600)), (nat_lit 83, Int.ofNat (nat_lit 389970806400)), (nat_lit 88, Int.ofNat (nat_lit 8898776208000)), (nat_lit 89, Int.ofNat (nat_lit 16329426810624)), (nat_lit 90, Int.ofNat (nat_lit 16994415513600)), (nat_lit 91, Int.ofNat (nat_lit 17667078912000)), (nat_lit 92, Int.ofNat (nat_lit 18339742310400)), (nat_lit 93, Int.ofNat (nat_lit 19012405708800)), (nat_lit 94, Int.ofNat (nat_lit 19685069107200)), (nat_lit 95, Int.ofNat (nat_lit 20357732505600)), (nat_lit 96, Int.ofNat (nat_lit 21233148865600)), (nat_lit 97, Int.ofNat (nat_lit 22067177025600)), (nat_lit 98, Int.ofNat (nat_lit 22681852200000)), (nat_lit 99, Int.ofNat (nat_lit 25767067334400)), (nat_lit 100, Int.ofNat (nat_lit 17557535532600)), (nat_lit 101, Int.ofNat (nat_lit 13074308755200)), (nat_lit 102, Int.ofNat (nat_lit 6011898921000)), (nat_lit 103, Int.ofNat (nat_lit 7268672867400)), (nat_lit 104, Int.ofNat (nat_lit 2531397393000)), (nat_lit 110, Int.ofNat (nat_lit 10430034421248)), (nat_lit 111, Int.ofNat (nat_lit 18863725537728)), (nat_lit 112, Int.ofNat (nat_lit 18055888573248)), (nat_lit 113, Int.ofNat (nat_lit 18662543424000)), (nat_lit 114, Int.ofNat (nat_lit 19685793960000)), (nat_lit 115, Int.ofNat (nat_lit 20344201920000)), (nat_lit 116, Int.ofNat (nat_lit 21185031168000)), (nat_lit 117, Int.ofNat (nat_lit 22373100702400)), (nat_lit 118, Int.ofNat (nat_lit 23206404009600)), (nat_lit 119, Int.ofNat (nat_lit 23885832700800)), (nat_lit 120, Int.ofNat (nat_lit 27533078906688)), (nat_lit 121, Int.ofNat (nat_lit 19930254363648)), (nat_lit 122, Int.ofNat (nat_lit 16772949095616)), (nat_lit 123, Int.ofNat (nat_lit 10592587378944)), (nat_lit 124, Int.ofNat (nat_lit 11062689626880)), (nat_lit 125, Int.ofNat (nat_lit 7775809398144)), (nat_lit 132, Int.ofNat (nat_lit 13029789427200)), (nat_lit 133, Int.ofNat (nat_lit 22027546931328)), (nat_lit 134, Int.ofNat (nat_lit 20547763034400)), (nat_lit 135, Int.ofNat (nat_lit 20553442761600)), (nat_lit 136, Int.ofNat (nat_lit 21299316292800)), (nat_lit 137, Int.ofNat (nat_lit 22058417203200)), (nat_lit 138, Int.ofNat (nat_lit 23415680646400))]
theorem block004_data_flat159_step : block004_data_flat159 = (CoefficientMerge.trim block004_data_flat158) := by decide +kernel
theorem block004_data_flat159_original : block004_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded))))))))) := by
  rw [block004_data_flat159_step, block004_data_flat158_original]
theorem block004_data : block004 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)))))))) := by
  have h : block004 = block004_data_flat159 := by decide +kernel
  exact h.trans block004_data_flat159_original
theorem block004_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block004 := by
  rw [block004_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0176Coded_nonneg g hg hA hB) (atom0177Coded_nonneg g hg hA hB)) (add_nonneg (atom0178Coded_nonneg g hg hA hB) (add_nonneg (atom0179Coded_nonneg g hg hA hB) (atom0180Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0181Coded_nonneg g hg hA hB) (atom0182Coded_nonneg g hg hA hB)) (add_nonneg (atom0183Coded_nonneg g hg hA hB) (add_nonneg (atom0184Coded_nonneg g hg hA hB) (atom0185Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0186Coded_nonneg g hg hA hB) (atom0187Coded_nonneg g hg hA hB)) (add_nonneg (atom0188Coded_nonneg g hg hA hB) (add_nonneg (atom0189Coded_nonneg g hg hA hB) (atom0190Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0191Coded_nonneg g hg hA hB) (atom0192Coded_nonneg g hg hA hB)) (add_nonneg (atom0193Coded_nonneg g hg hA hB) (add_nonneg (atom0194Coded_nonneg g hg hA hB) (atom0195Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0196Coded_nonneg g hg hA hB) (atom0197Coded_nonneg g hg hA hB)) (add_nonneg (atom0198Coded_nonneg g hg hA hB) (add_nonneg (atom0199Coded_nonneg g hg hA hB) (atom0200Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0201Coded_nonneg g hg hA hB) (atom0202Coded_nonneg g hg hA hB)) (add_nonneg (atom0203Coded_nonneg g hg hA hB) (add_nonneg (atom0204Coded_nonneg g hg hA hB) (atom0205Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0206Coded_nonneg g hg hA hB) (atom0207Coded_nonneg g hg hA hB)) (add_nonneg (atom0208Coded_nonneg g hg hA hB) (add_nonneg (atom0209Coded_nonneg g hg hA hB) (atom0210Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0211Coded_nonneg g hg hA hB) (atom0212Coded_nonneg g hg hA hB)) (add_nonneg (atom0213Coded_nonneg g hg hA hB) (add_nonneg (atom0214Coded_nonneg g hg hA hB) (atom0215Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0216Coded_nonneg g hg hA hB) (atom0217Coded_nonneg g hg hA hB)) (add_nonneg (atom0218Coded_nonneg g hg hA hB) (add_nonneg (atom0219Coded_nonneg g hg hA hB) (atom0220Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0221Coded_nonneg g hg hA hB) (atom0222Coded_nonneg g hg hA hB)) (add_nonneg (atom0223Coded_nonneg g hg hA hB) (add_nonneg (atom0224Coded_nonneg g hg hA hB) (atom0225Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0226Coded_nonneg g hg hA hB) (atom0227Coded_nonneg g hg hA hB)) (add_nonneg (atom0228Coded_nonneg g hg hA hB) (add_nonneg (atom0229Coded_nonneg g hg hA hB) (atom0230Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0231Coded_nonneg g hg hA hB) (atom0232Coded_nonneg g hg hA hB)) (add_nonneg (atom0233Coded_nonneg g hg hA hB) (add_nonneg (atom0234Coded_nonneg g hg hA hB) (atom0235Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0236Coded_nonneg g hg hA hB) (atom0237Coded_nonneg g hg hA hB)) (add_nonneg (atom0238Coded_nonneg g hg hA hB) (add_nonneg (atom0239Coded_nonneg g hg hA hB) (atom0240Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0241Coded_nonneg g hg hA hB) (atom0242Coded_nonneg g hg hA hB)) (add_nonneg (atom0243Coded_nonneg g hg hA hB) (add_nonneg (atom0244Coded_nonneg g hg hA hB) (atom0245Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0246Coded_nonneg g hg hA hB) (atom0247Coded_nonneg g hg hA hB)) (add_nonneg (atom0248Coded_nonneg g hg hA hB) (add_nonneg (atom0249Coded_nonneg g hg hA hB) (atom0250Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0251Coded_nonneg g hg hA hB) (atom0252Coded_nonneg g hg hA hB)) (add_nonneg (atom0253Coded_nonneg g hg hA hB) (add_nonneg (atom0254Coded_nonneg g hg hA hB) (atom0255Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
