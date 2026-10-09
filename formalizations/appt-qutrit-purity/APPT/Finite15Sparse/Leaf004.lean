-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0313 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0313 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0313 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0313_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61263360 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313Coded : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 1))]
theorem atom0313Coded_decode : atom0313 = SparsePolynomial.decodeCubic 15 atom0313Coded := by decide +kernel
theorem atom0313Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61263360 : Int) atom0313Coded) := by
  have h := atom0313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0314 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0314 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0314 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0314_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102746880 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314Coded : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 1))]
theorem atom0314Coded_decode : atom0314 = SparsePolynomial.decodeCubic 15 atom0314Coded := by decide +kernel
theorem atom0314Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (102746880 : Int) atom0314Coded) := by
  have h := atom0314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0315 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0315 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0315 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0315_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68907600 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315Coded : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 1))]
theorem atom0315Coded_decode : atom0315 = SparsePolynomial.decodeCubic 15 atom0315Coded := by decide +kernel
theorem atom0315Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (68907600 : Int) atom0315Coded) := by
  have h := atom0315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0316 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0316 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0316 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0316_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86732640 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316Coded : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 1))]
theorem atom0316Coded_decode : atom0316 = SparsePolynomial.decodeCubic 15 atom0316Coded := by decide +kernel
theorem atom0316Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86732640 : Int) atom0316Coded) := by
  have h := atom0316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0317 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0317 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0317 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0317_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84196080 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317Coded : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 1))]
theorem atom0317Coded_decode : atom0317 = SparsePolynomial.decodeCubic 15 atom0317Coded := by decide +kernel
theorem atom0317Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (84196080 : Int) atom0317Coded) := by
  have h := atom0317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0318 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0318 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0318 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0318_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87441840 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318Coded : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 1))]
theorem atom0318Coded_decode : atom0318 = SparsePolynomial.decodeCubic 15 atom0318Coded := by decide +kernel
theorem atom0318Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87441840 : Int) atom0318Coded) := by
  have h := atom0318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0319 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0319 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0319 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0319_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113022000 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319Coded : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 1))]
theorem atom0319Coded_decode : atom0319 = SparsePolynomial.decodeCubic 15 atom0319Coded := by decide +kernel
theorem atom0319Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (113022000 : Int) atom0319Coded) := by
  have h := atom0319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0320 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0320 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0320 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0320_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38949120 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320Coded : CoefficientMerge.Poly := [(nat_lit 546, Int.ofNat (nat_lit 1))]
theorem atom0320Coded_decode : atom0320 = SparsePolynomial.decodeCubic 15 atom0320Coded := by decide +kernel
theorem atom0320Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38949120 : Int) atom0320Coded) := by
  have h := atom0320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0321 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0321 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0321 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0321_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76222080 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321Coded : CoefficientMerge.Poly := [(nat_lit 547, Int.ofNat (nat_lit 1))]
theorem atom0321Coded_decode : atom0321 = SparsePolynomial.decodeCubic 15 atom0321Coded := by decide +kernel
theorem atom0321Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (76222080 : Int) atom0321Coded) := by
  have h := atom0321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0322 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0322 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0322 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0322_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74545920 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322Coded : CoefficientMerge.Poly := [(nat_lit 548, Int.ofNat (nat_lit 1))]
theorem atom0322Coded_decode : atom0322 = SparsePolynomial.decodeCubic 15 atom0322Coded := by decide +kernel
theorem atom0322Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74545920 : Int) atom0322Coded) := by
  have h := atom0322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0323 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0323 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0323 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0323_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108552960 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323Coded : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 1))]
theorem atom0323Coded_decode : atom0323 = SparsePolynomial.decodeCubic 15 atom0323Coded := by decide +kernel
theorem atom0323Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (108552960 : Int) atom0323Coded) := by
  have h := atom0323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0324 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0324 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0324 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0324_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81308880 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324Coded : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 1))]
theorem atom0324Coded_decode : atom0324 = SparsePolynomial.decodeCubic 15 atom0324Coded := by decide +kernel
theorem atom0324Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (81308880 : Int) atom0324Coded) := by
  have h := atom0324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0325 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0325 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0325 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0325_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99692640 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325Coded : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 1))]
theorem atom0325Coded_decode : atom0325 = SparsePolynomial.decodeCubic 15 atom0325Coded := by decide +kernel
theorem atom0325Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (99692640 : Int) atom0325Coded) := by
  have h := atom0325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0326 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0326 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0326 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0326_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98187120 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326Coded : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 1))]
theorem atom0326Coded_decode : atom0326 = SparsePolynomial.decodeCubic 15 atom0326Coded := by decide +kernel
theorem atom0326Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98187120 : Int) atom0326Coded) := by
  have h := atom0326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0327 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0327 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0327 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0327_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103051440 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327Coded : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 1))]
theorem atom0327Coded_decode : atom0327 = SparsePolynomial.decodeCubic 15 atom0327Coded := by decide +kernel
theorem atom0327Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (103051440 : Int) atom0327Coded) := by
  have h := atom0327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0328 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0328 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0328 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0328_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130250160 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328Coded : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 1))]
theorem atom0328Coded_decode : atom0328 = SparsePolynomial.decodeCubic 15 atom0328Coded := by decide +kernel
theorem atom0328Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (130250160 : Int) atom0328Coded) := by
  have h := atom0328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0329 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0329 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0329 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0329_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47187840 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329Coded : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 1))]
theorem atom0329Coded_decode : atom0329 = SparsePolynomial.decodeCubic 15 atom0329Coded := by decide +kernel
theorem atom0329Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47187840 : Int) atom0329Coded) := by
  have h := atom0329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0330 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0330 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0330 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0330_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89790720 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330Coded : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 1))]
theorem atom0330Coded_decode : atom0330 = SparsePolynomial.decodeCubic 15 atom0330Coded := by decide +kernel
theorem atom0330Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (89790720 : Int) atom0330Coded) := by
  have h := atom0330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0331 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0331 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0331 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0331_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116319360 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331Coded : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 1))]
theorem atom0331Coded_decode : atom0331 = SparsePolynomial.decodeCubic 15 atom0331Coded := by decide +kernel
theorem atom0331Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (116319360 : Int) atom0331Coded) := by
  have h := atom0331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0332 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0332 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0332 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0332_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (92273280 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332Coded : CoefficientMerge.Poly := [(nat_lit 565, Int.ofNat (nat_lit 1))]
theorem atom0332Coded_decode : atom0332 = SparsePolynomial.decodeCubic 15 atom0332Coded := by decide +kernel
theorem atom0332Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (92273280 : Int) atom0332Coded) := by
  have h := atom0332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0333 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0333 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0333 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0333_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112652640 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333Coded : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 1))]
theorem atom0333Coded_decode : atom0333 = SparsePolynomial.decodeCubic 15 atom0333Coded := by decide +kernel
theorem atom0333Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (112652640 : Int) atom0333Coded) := by
  have h := atom0333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0334 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0334 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0334 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0334_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106327680 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334Coded : CoefficientMerge.Poly := [(nat_lit 567, Int.ofNat (nat_lit 1))]
theorem atom0334Coded_decode : atom0334 = SparsePolynomial.decodeCubic 15 atom0334Coded := by decide +kernel
theorem atom0334Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (106327680 : Int) atom0334Coded) := by
  have h := atom0334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0335 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0335 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110265600 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335Coded : CoefficientMerge.Poly := [(nat_lit 568, Int.ofNat (nat_lit 1))]
theorem atom0335Coded_decode : atom0335 = SparsePolynomial.decodeCubic 15 atom0335Coded := by decide +kernel
theorem atom0335Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (110265600 : Int) atom0335Coded) := by
  have h := atom0335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0336 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0336 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136537920 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336Coded : CoefficientMerge.Poly := [(nat_lit 569, Int.ofNat (nat_lit 1))]
theorem atom0336Coded_decode : atom0336 = SparsePolynomial.decodeCubic 15 atom0336Coded := by decide +kernel
theorem atom0336Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (136537920 : Int) atom0336Coded) := by
  have h := atom0336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0337 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0337 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54432000 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337Coded : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 1))]
theorem atom0337Coded_decode : atom0337 = SparsePolynomial.decodeCubic 15 atom0337Coded := by decide +kernel
theorem atom0337Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (54432000 : Int) atom0337Coded) := by
  have h := atom0337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0338 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0338 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131245920 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338Coded : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 1))]
theorem atom0338Coded_decode : atom0338 = SparsePolynomial.decodeCubic 15 atom0338Coded := by decide +kernel
theorem atom0338Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (131245920 : Int) atom0338Coded) := by
  have h := atom0338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0339 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0339 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102967200 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339Coded : CoefficientMerge.Poly := [(nat_lit 580, Int.ofNat (nat_lit 1))]
theorem atom0339Coded_decode : atom0339 = SparsePolynomial.decodeCubic 15 atom0339Coded := by decide +kernel
theorem atom0339Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (102967200 : Int) atom0339Coded) := by
  have h := atom0339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0340 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0340 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125612640 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340Coded : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 1))]
theorem atom0340Coded_decode : atom0340 = SparsePolynomial.decodeCubic 15 atom0340Coded := by decide +kernel
theorem atom0340Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (125612640 : Int) atom0340Coded) := by
  have h := atom0340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0341 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0341 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117365760 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341Coded : CoefficientMerge.Poly := [(nat_lit 582, Int.ofNat (nat_lit 1))]
theorem atom0341Coded_decode : atom0341 = SparsePolynomial.decodeCubic 15 atom0341Coded := by decide +kernel
theorem atom0341Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (117365760 : Int) atom0341Coded) := by
  have h := atom0341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0342 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0342 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107917920 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342Coded : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 1))]
theorem atom0342Coded_decode : atom0342 = SparsePolynomial.decodeCubic 15 atom0342Coded := by decide +kernel
theorem atom0342Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (107917920 : Int) atom0342Coded) := by
  have h := atom0342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0343 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0343 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (160228800 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343Coded : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 1))]
theorem atom0343Coded_decode : atom0343 = SparsePolynomial.decodeCubic 15 atom0343Coded := by decide +kernel
theorem atom0343Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (160228800 : Int) atom0343Coded) := by
  have h := atom0343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0344 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0344 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90201600 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344Coded : CoefficientMerge.Poly := [(nat_lit 594, Int.ofNat (nat_lit 1))]
theorem atom0344Coded_decode : atom0344 = SparsePolynomial.decodeCubic 15 atom0344Coded := by decide +kernel
theorem atom0344Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90201600 : Int) atom0344Coded) := by
  have h := atom0344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0345 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0345 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146759040 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345Coded : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 1))]
theorem atom0345Coded_decode : atom0345 = SparsePolynomial.decodeCubic 15 atom0345Coded := by decide +kernel
theorem atom0345Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (146759040 : Int) atom0345Coded) := by
  have h := atom0345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0346 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0346 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193004640 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346Coded : CoefficientMerge.Poly := [(nat_lit 596, Int.ofNat (nat_lit 1))]
theorem atom0346Coded_decode : atom0346 = SparsePolynomial.decodeCubic 15 atom0346Coded := by decide +kernel
theorem atom0346Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (193004640 : Int) atom0346Coded) := by
  have h := atom0346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0347 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0347 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188334720 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347Coded : CoefficientMerge.Poly := [(nat_lit 597, Int.ofNat (nat_lit 1))]
theorem atom0347Coded_decode : atom0347 = SparsePolynomial.decodeCubic 15 atom0347Coded := by decide +kernel
theorem atom0347Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (188334720 : Int) atom0347Coded) := by
  have h := atom0347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0348 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0348 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110393280 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348Coded : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 1))]
theorem atom0348Coded_decode : atom0348 = SparsePolynomial.decodeCubic 15 atom0348Coded := by decide +kernel
theorem atom0348Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (110393280 : Int) atom0348Coded) := by
  have h := atom0348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0349 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0349 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182864520 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349Coded : CoefficientMerge.Poly := [(nat_lit 599, Int.ofNat (nat_lit 1))]
theorem atom0349Coded_decode : atom0349 = SparsePolynomial.decodeCubic 15 atom0349Coded := by decide +kernel
theorem atom0349Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (182864520 : Int) atom0349Coded) := by
  have h := atom0349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0350 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0350 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67526784 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350Coded : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 1))]
theorem atom0350Coded_decode : atom0350 = SparsePolynomial.decodeCubic 15 atom0350Coded := by decide +kernel
theorem atom0350Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (67526784 : Int) atom0350Coded) := by
  have h := atom0350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0351 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0351 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158776200 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351Coded : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 1))]
theorem atom0351Coded_decode : atom0351 = SparsePolynomial.decodeCubic 15 atom0351Coded := by decide +kernel
theorem atom0351Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (158776200 : Int) atom0351Coded) := by
  have h := atom0351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0352 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0352 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177655680 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352Coded : CoefficientMerge.Poly := [(nat_lit 612, Int.ofNat (nat_lit 1))]
theorem atom0352Coded_decode : atom0352 = SparsePolynomial.decodeCubic 15 atom0352Coded := by decide +kernel
theorem atom0352Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (177655680 : Int) atom0352Coded) := by
  have h := atom0352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0353 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0353 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120372480 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353Coded : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 1))]
theorem atom0353Coded_decode : atom0353 = SparsePolynomial.decodeCubic 15 atom0353Coded := by decide +kernel
theorem atom0353Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (120372480 : Int) atom0353Coded) := by
  have h := atom0353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0354 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0354 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150013080 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354Coded : CoefficientMerge.Poly := [(nat_lit 614, Int.ofNat (nat_lit 1))]
theorem atom0354Coded_decode : atom0354 = SparsePolynomial.decodeCubic 15 atom0354Coded := by decide +kernel
theorem atom0354Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (150013080 : Int) atom0354Coded) := by
  have h := atom0354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0355 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0355 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102218760 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355Coded : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 1))]
theorem atom0355Coded_decode : atom0355 = SparsePolynomial.decodeCubic 15 atom0355Coded := by decide +kernel
theorem atom0355Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (102218760 : Int) atom0355Coded) := by
  have h := atom0355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0356 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0356 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172461960 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356Coded : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 1))]
theorem atom0356Coded_decode : atom0356 = SparsePolynomial.decodeCubic 15 atom0356Coded := by decide +kernel
theorem atom0356Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (172461960 : Int) atom0356Coded) := by
  have h := atom0356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0357 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0357 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115864560 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357Coded : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 1))]
theorem atom0357Coded_decode : atom0357 = SparsePolynomial.decodeCubic 15 atom0357Coded := by decide +kernel
theorem atom0357Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (115864560 : Int) atom0357Coded) := by
  have h := atom0357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0358 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0358 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154996200 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358Coded : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1))]
theorem atom0358Coded_decode : atom0358 = SparsePolynomial.decodeCubic 15 atom0358Coded := by decide +kernel
theorem atom0358Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (154996200 : Int) atom0358Coded) := by
  have h := atom0358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0359 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0359 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64540800 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359Coded : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 1))]
theorem atom0359Coded_decode : atom0359 = SparsePolynomial.decodeCubic 15 atom0359Coded := by decide +kernel
theorem atom0359Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64540800 : Int) atom0359Coded) := by
  have h := atom0359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0360 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0360 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90966240 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360Coded : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 1))]
theorem atom0360Coded_decode : atom0360 = SparsePolynomial.decodeCubic 15 atom0360Coded := by decide +kernel
theorem atom0360Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90966240 : Int) atom0360Coded) := by
  have h := atom0360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0361 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0361 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136631880 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361Coded : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 1))]
theorem atom0361Coded_decode : atom0361 = SparsePolynomial.decodeCubic 15 atom0361Coded := by decide +kernel
theorem atom0361Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (136631880 : Int) atom0361Coded) := by
  have h := atom0361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0362 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0362 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15655680 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362Coded : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 1))]
theorem atom0362Coded_decode : atom0362 = SparsePolynomial.decodeCubic 15 atom0362Coded := by decide +kernel
theorem atom0362Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15655680 : Int) atom0362Coded) := by
  have h := atom0362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0363 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0363 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78867000 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363Coded : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 1))]
theorem atom0363Coded_decode : atom0363 = SparsePolynomial.decodeCubic 15 atom0363Coded := by decide +kernel
theorem atom0363Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (78867000 : Int) atom0363Coded) := by
  have h := atom0363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0364 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0364 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55821960 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364Coded : CoefficientMerge.Poly := [(nat_lit 674, Int.ofNat (nat_lit 1))]
theorem atom0364Coded_decode : atom0364 = SparsePolynomial.decodeCubic 15 atom0364Coded := by decide +kernel
theorem atom0364Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (55821960 : Int) atom0364Coded) := by
  have h := atom0364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0365 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0365 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1382400 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365Coded : CoefficientMerge.Poly := [(nat_lit 723, Int.ofNat (nat_lit 1))]
theorem atom0365Coded_decode : atom0365 = SparsePolynomial.decodeCubic 15 atom0365Coded := by decide +kernel
theorem atom0365Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1382400 : Int) atom0365Coded) := by
  have h := atom0365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0366 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0366 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (898560 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366Coded : CoefficientMerge.Poly := [(nat_lit 724, Int.ofNat (nat_lit 1))]
theorem atom0366Coded_decode : atom0366 = SparsePolynomial.decodeCubic 15 atom0366Coded := by decide +kernel
theorem atom0366Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (898560 : Int) atom0366Coded) := by
  have h := atom0366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0367 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0367 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (449280 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367Coded : CoefficientMerge.Poly := [(nat_lit 725, Int.ofNat (nat_lit 1))]
theorem atom0367Coded_decode : atom0367 = SparsePolynomial.decodeCubic 15 atom0367Coded := by decide +kernel
theorem atom0367Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (449280 : Int) atom0367Coded) := by
  have h := atom0367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0368 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0368 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25693200 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368Coded : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 1))]
theorem atom0368Coded_decode : atom0368 = SparsePolynomial.decodeCubic 15 atom0368Coded := by decide +kernel
theorem atom0368Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (25693200 : Int) atom0368Coded) := by
  have h := atom0368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0369 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0369 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9257760 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369Coded : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 1))]
theorem atom0369Coded_decode : atom0369 = SparsePolynomial.decodeCubic 15 atom0369Coded := by decide +kernel
theorem atom0369Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (9257760 : Int) atom0369Coded) := by
  have h := atom0369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0370 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0370 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4746240 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370Coded : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 1))]
theorem atom0370Coded_decode : atom0370 = SparsePolynomial.decodeCubic 15 atom0370Coded := by decide +kernel
theorem atom0370Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (4746240 : Int) atom0370Coded) := by
  have h := atom0370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0371 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0371 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2148480 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371Coded : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 1))]
theorem atom0371Coded_decode : atom0371 = SparsePolynomial.decodeCubic 15 atom0371Coded := by decide +kernel
theorem atom0371Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2148480 : Int) atom0371Coded) := by
  have h := atom0371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0372 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0372 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3600000 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372Coded : CoefficientMerge.Poly := [(nat_lit 741, Int.ofNat (nat_lit 1))]
theorem atom0372Coded_decode : atom0372 = SparsePolynomial.decodeCubic 15 atom0372Coded := by decide +kernel
theorem atom0372Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3600000 : Int) atom0372Coded) := by
  have h := atom0372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0373 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0373 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5500800 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373Coded : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 1))]
theorem atom0373Coded_decode : atom0373 = SparsePolynomial.decodeCubic 15 atom0373Coded := by decide +kernel
theorem atom0373Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5500800 : Int) atom0373Coded) := by
  have h := atom0373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0374 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0374 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7401600 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374Coded : CoefficientMerge.Poly := [(nat_lit 743, Int.ofNat (nat_lit 1))]
theorem atom0374Coded_decode : atom0374 = SparsePolynomial.decodeCubic 15 atom0374Coded := by decide +kernel
theorem atom0374Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (7401600 : Int) atom0374Coded) := by
  have h := atom0374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0375 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0375 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56678400 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375Coded : CoefficientMerge.Poly := [(nat_lit 744, Int.ofNat (nat_lit 1))]
theorem atom0375Coded_decode : atom0375 = SparsePolynomial.decodeCubic 15 atom0375Coded := by decide +kernel
theorem atom0375Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (56678400 : Int) atom0375Coded) := by
  have h := atom0375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0376 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0376 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16715520 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376Coded : CoefficientMerge.Poly := [(nat_lit 745, Int.ofNat (nat_lit 1))]
theorem atom0376Coded_decode : atom0376 = SparsePolynomial.decodeCubic 15 atom0376Coded := by decide +kernel
theorem atom0376Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16715520 : Int) atom0376Coded) := by
  have h := atom0376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0377 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0377 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35445600 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377Coded : CoefficientMerge.Poly := [(nat_lit 746, Int.ofNat (nat_lit 1))]
theorem atom0377Coded_decode : atom0377 = SparsePolynomial.decodeCubic 15 atom0377Coded := by decide +kernel
theorem atom0377Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (35445600 : Int) atom0377Coded) := by
  have h := atom0377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0378 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0378 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31541760 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378Coded : CoefficientMerge.Poly := [(nat_lit 747, Int.ofNat (nat_lit 1))]
theorem atom0378Coded_decode : atom0378 = SparsePolynomial.decodeCubic 15 atom0378Coded := by decide +kernel
theorem atom0378Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (31541760 : Int) atom0378Coded) := by
  have h := atom0378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0379 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0379 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40792320 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379Coded : CoefficientMerge.Poly := [(nat_lit 748, Int.ofNat (nat_lit 1))]
theorem atom0379Coded_decode : atom0379 = SparsePolynomial.decodeCubic 15 atom0379Coded := by decide +kernel
theorem atom0379Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40792320 : Int) atom0379Coded) := by
  have h := atom0379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0380 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0380 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50042880 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380Coded : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 1))]
theorem atom0380Coded_decode : atom0380 = SparsePolynomial.decodeCubic 15 atom0380Coded := by decide +kernel
theorem atom0380Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (50042880 : Int) atom0380Coded) := by
  have h := atom0380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0381 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0381 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8098560 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381Coded : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 1))]
theorem atom0381Coded_decode : atom0381 = SparsePolynomial.decodeCubic 15 atom0381Coded := by decide +kernel
theorem atom0381Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (8098560 : Int) atom0381Coded) := by
  have h := atom0381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0382 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0382 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16456320 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382Coded : CoefficientMerge.Poly := [(nat_lit 756, Int.ofNat (nat_lit 1))]
theorem atom0382Coded_decode : atom0382 = SparsePolynomial.decodeCubic 15 atom0382Coded := by decide +kernel
theorem atom0382Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16456320 : Int) atom0382Coded) := by
  have h := atom0382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0383 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0383 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19065600 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383Coded : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 1))]
theorem atom0383Coded_decode : atom0383 = SparsePolynomial.decodeCubic 15 atom0383Coded := by decide +kernel
theorem atom0383Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (19065600 : Int) atom0383Coded) := by
  have h := atom0383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0384 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0384 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21674880 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384Coded : CoefficientMerge.Poly := [(nat_lit 758, Int.ofNat (nat_lit 1))]
theorem atom0384Coded_decode : atom0384 = SparsePolynomial.decodeCubic 15 atom0384Coded := by decide +kernel
theorem atom0384Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (21674880 : Int) atom0384Coded) := by
  have h := atom0384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0385 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0385 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64419840 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385Coded : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 1))]
theorem atom0385Coded_decode : atom0385 = SparsePolynomial.decodeCubic 15 atom0385Coded := by decide +kernel
theorem atom0385Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64419840 : Int) atom0385Coded) := by
  have h := atom0385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0386 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0386 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35062560 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386Coded : CoefficientMerge.Poly := [(nat_lit 760, Int.ofNat (nat_lit 1))]
theorem atom0386Coded_decode : atom0386 = SparsePolynomial.decodeCubic 15 atom0386Coded := by decide +kernel
theorem atom0386Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (35062560 : Int) atom0386Coded) := by
  have h := atom0386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0387 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0387 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52725600 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387Coded : CoefficientMerge.Poly := [(nat_lit 761, Int.ofNat (nat_lit 1))]
theorem atom0387Coded_decode : atom0387 = SparsePolynomial.decodeCubic 15 atom0387Coded := by decide +kernel
theorem atom0387Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (52725600 : Int) atom0387Coded) := by
  have h := atom0387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0388 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0388 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56619360 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388Coded : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 1))]
theorem atom0388Coded_decode : atom0388 = SparsePolynomial.decodeCubic 15 atom0388Coded := by decide +kernel
theorem atom0388Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (56619360 : Int) atom0388Coded) := by
  have h := atom0388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0389 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0389 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70120800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389Coded : CoefficientMerge.Poly := [(nat_lit 763, Int.ofNat (nat_lit 1))]
theorem atom0389Coded_decode : atom0389 = SparsePolynomial.decodeCubic 15 atom0389Coded := by decide +kernel
theorem atom0389Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (70120800 : Int) atom0389Coded) := by
  have h := atom0389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0390 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0390 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83622240 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390Coded : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 1))]
theorem atom0390Coded_decode : atom0390 = SparsePolynomial.decodeCubic 15 atom0390Coded := by decide +kernel
theorem atom0390Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (83622240 : Int) atom0390Coded) := by
  have h := atom0390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0391 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0391 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15724800 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391Coded : CoefficientMerge.Poly := [(nat_lit 771, Int.ofNat (nat_lit 1))]
theorem atom0391Coded_decode : atom0391 = SparsePolynomial.decodeCubic 15 atom0391Coded := by decide +kernel
theorem atom0391Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15724800 : Int) atom0391Coded) := by
  have h := atom0391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0392 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0392 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33575040 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392Coded : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 1))]
theorem atom0392Coded_decode : atom0392 = SparsePolynomial.decodeCubic 15 atom0392Coded := by decide +kernel
theorem atom0392Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33575040 : Int) atom0392Coded) := by
  have h := atom0392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block004 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920)), (nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280)), (nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920)), (nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680)), (nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680)), (nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000)), (nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320)), (nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
def block004_data_flat000 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360))]
theorem block004_data_flat000_step : block004_data_flat000 = (CoefficientMerge.scale (61263360 : Int) atom0313Coded) := by decide +kernel
theorem block004_data_flat000_original : block004_data_flat000 = (CoefficientMerge.scale (61263360 : Int) atom0313Coded) := by
  rw [block004_data_flat000_step]
def block004_data_flat001 : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 102746880))]
theorem block004_data_flat001_step : block004_data_flat001 = (CoefficientMerge.scale (102746880 : Int) atom0314Coded) := by decide +kernel
theorem block004_data_flat001_original : block004_data_flat001 = (CoefficientMerge.scale (102746880 : Int) atom0314Coded) := by
  rw [block004_data_flat001_step]
def block004_data_flat002 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880))]
theorem block004_data_flat002_step : block004_data_flat002 = (CoefficientMerge.fastMerge block004_data_flat000 block004_data_flat001) := by decide +kernel
theorem block004_data_flat002_original : block004_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) := by
  rw [block004_data_flat002_step, block004_data_flat000_original, block004_data_flat001_original]
def block004_data_flat003 : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 68907600))]
theorem block004_data_flat003_step : block004_data_flat003 = (CoefficientMerge.scale (68907600 : Int) atom0315Coded) := by decide +kernel
theorem block004_data_flat003_original : block004_data_flat003 = (CoefficientMerge.scale (68907600 : Int) atom0315Coded) := by
  rw [block004_data_flat003_step]
def block004_data_flat004 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 86732640))]
theorem block004_data_flat004_step : block004_data_flat004 = (CoefficientMerge.scale (86732640 : Int) atom0316Coded) := by decide +kernel
theorem block004_data_flat004_original : block004_data_flat004 = (CoefficientMerge.scale (86732640 : Int) atom0316Coded) := by
  rw [block004_data_flat004_step]
def block004_data_flat005 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 84196080))]
theorem block004_data_flat005_step : block004_data_flat005 = (CoefficientMerge.scale (84196080 : Int) atom0317Coded) := by decide +kernel
theorem block004_data_flat005_original : block004_data_flat005 = (CoefficientMerge.scale (84196080 : Int) atom0317Coded) := by
  rw [block004_data_flat005_step]
def block004_data_flat006 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080))]
theorem block004_data_flat006_step : block004_data_flat006 = (CoefficientMerge.fastMerge block004_data_flat004 block004_data_flat005) := by decide +kernel
theorem block004_data_flat006_original : block004_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)) := by
  rw [block004_data_flat006_step, block004_data_flat004_original, block004_data_flat005_original]
def block004_data_flat007 : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080))]
theorem block004_data_flat007_step : block004_data_flat007 = (CoefficientMerge.fastMerge block004_data_flat003 block004_data_flat006) := by decide +kernel
theorem block004_data_flat007_original : block004_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded))) := by
  rw [block004_data_flat007_step, block004_data_flat003_original, block004_data_flat006_original]
def block004_data_flat008 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080))]
theorem block004_data_flat008_step : block004_data_flat008 = (CoefficientMerge.fastMerge block004_data_flat002 block004_data_flat007) := by decide +kernel
theorem block004_data_flat008_original : block004_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) := by
  rw [block004_data_flat008_step, block004_data_flat002_original, block004_data_flat007_original]
def block004_data_flat009 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 87441840))]
theorem block004_data_flat009_step : block004_data_flat009 = (CoefficientMerge.scale (87441840 : Int) atom0318Coded) := by decide +kernel
theorem block004_data_flat009_original : block004_data_flat009 = (CoefficientMerge.scale (87441840 : Int) atom0318Coded) := by
  rw [block004_data_flat009_step]
def block004_data_flat010 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 113022000))]
theorem block004_data_flat010_step : block004_data_flat010 = (CoefficientMerge.scale (113022000 : Int) atom0319Coded) := by decide +kernel
theorem block004_data_flat010_original : block004_data_flat010 = (CoefficientMerge.scale (113022000 : Int) atom0319Coded) := by
  rw [block004_data_flat010_step]
def block004_data_flat011 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000))]
theorem block004_data_flat011_step : block004_data_flat011 = (CoefficientMerge.fastMerge block004_data_flat009 block004_data_flat010) := by decide +kernel
theorem block004_data_flat011_original : block004_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) := by
  rw [block004_data_flat011_step, block004_data_flat009_original, block004_data_flat010_original]
def block004_data_flat012 : CoefficientMerge.Poly := [(nat_lit 546, Int.ofNat (nat_lit 38949120))]
theorem block004_data_flat012_step : block004_data_flat012 = (CoefficientMerge.scale (38949120 : Int) atom0320Coded) := by decide +kernel
theorem block004_data_flat012_original : block004_data_flat012 = (CoefficientMerge.scale (38949120 : Int) atom0320Coded) := by
  rw [block004_data_flat012_step]
def block004_data_flat013 : CoefficientMerge.Poly := [(nat_lit 547, Int.ofNat (nat_lit 76222080))]
theorem block004_data_flat013_step : block004_data_flat013 = (CoefficientMerge.scale (76222080 : Int) atom0321Coded) := by decide +kernel
theorem block004_data_flat013_original : block004_data_flat013 = (CoefficientMerge.scale (76222080 : Int) atom0321Coded) := by
  rw [block004_data_flat013_step]
def block004_data_flat014 : CoefficientMerge.Poly := [(nat_lit 548, Int.ofNat (nat_lit 74545920))]
theorem block004_data_flat014_step : block004_data_flat014 = (CoefficientMerge.scale (74545920 : Int) atom0322Coded) := by decide +kernel
theorem block004_data_flat014_original : block004_data_flat014 = (CoefficientMerge.scale (74545920 : Int) atom0322Coded) := by
  rw [block004_data_flat014_step]
def block004_data_flat015 : CoefficientMerge.Poly := [(nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920))]
theorem block004_data_flat015_step : block004_data_flat015 = (CoefficientMerge.fastMerge block004_data_flat013 block004_data_flat014) := by decide +kernel
theorem block004_data_flat015_original : block004_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded)) := by
  rw [block004_data_flat015_step, block004_data_flat013_original, block004_data_flat014_original]
def block004_data_flat016 : CoefficientMerge.Poly := [(nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920))]
theorem block004_data_flat016_step : block004_data_flat016 = (CoefficientMerge.fastMerge block004_data_flat012 block004_data_flat015) := by decide +kernel
theorem block004_data_flat016_original : block004_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))) := by
  rw [block004_data_flat016_step, block004_data_flat012_original, block004_data_flat015_original]
def block004_data_flat017 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920))]
theorem block004_data_flat017_step : block004_data_flat017 = (CoefficientMerge.fastMerge block004_data_flat011 block004_data_flat016) := by decide +kernel
theorem block004_data_flat017_original : block004_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded)))) := by
  rw [block004_data_flat017_step, block004_data_flat011_original, block004_data_flat016_original]
def block004_data_flat018 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920))]
theorem block004_data_flat018_step : block004_data_flat018 = (CoefficientMerge.fastMerge block004_data_flat008 block004_data_flat017) := by decide +kernel
theorem block004_data_flat018_original : block004_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) := by
  rw [block004_data_flat018_step, block004_data_flat008_original, block004_data_flat017_original]
def block004_data_flat019 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 108552960))]
theorem block004_data_flat019_step : block004_data_flat019 = (CoefficientMerge.scale (108552960 : Int) atom0323Coded) := by decide +kernel
theorem block004_data_flat019_original : block004_data_flat019 = (CoefficientMerge.scale (108552960 : Int) atom0323Coded) := by
  rw [block004_data_flat019_step]
def block004_data_flat020 : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 81308880))]
theorem block004_data_flat020_step : block004_data_flat020 = (CoefficientMerge.scale (81308880 : Int) atom0324Coded) := by decide +kernel
theorem block004_data_flat020_original : block004_data_flat020 = (CoefficientMerge.scale (81308880 : Int) atom0324Coded) := by
  rw [block004_data_flat020_step]
def block004_data_flat021 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880))]
theorem block004_data_flat021_step : block004_data_flat021 = (CoefficientMerge.fastMerge block004_data_flat019 block004_data_flat020) := by decide +kernel
theorem block004_data_flat021_original : block004_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) := by
  rw [block004_data_flat021_step, block004_data_flat019_original, block004_data_flat020_original]
def block004_data_flat022 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 99692640))]
theorem block004_data_flat022_step : block004_data_flat022 = (CoefficientMerge.scale (99692640 : Int) atom0325Coded) := by decide +kernel
theorem block004_data_flat022_original : block004_data_flat022 = (CoefficientMerge.scale (99692640 : Int) atom0325Coded) := by
  rw [block004_data_flat022_step]
def block004_data_flat023 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 98187120))]
theorem block004_data_flat023_step : block004_data_flat023 = (CoefficientMerge.scale (98187120 : Int) atom0326Coded) := by decide +kernel
theorem block004_data_flat023_original : block004_data_flat023 = (CoefficientMerge.scale (98187120 : Int) atom0326Coded) := by
  rw [block004_data_flat023_step]
def block004_data_flat024 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 103051440))]
theorem block004_data_flat024_step : block004_data_flat024 = (CoefficientMerge.scale (103051440 : Int) atom0327Coded) := by decide +kernel
theorem block004_data_flat024_original : block004_data_flat024 = (CoefficientMerge.scale (103051440 : Int) atom0327Coded) := by
  rw [block004_data_flat024_step]
def block004_data_flat025 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440))]
theorem block004_data_flat025_step : block004_data_flat025 = (CoefficientMerge.fastMerge block004_data_flat023 block004_data_flat024) := by decide +kernel
theorem block004_data_flat025_original : block004_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)) := by
  rw [block004_data_flat025_step, block004_data_flat023_original, block004_data_flat024_original]
def block004_data_flat026 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440))]
theorem block004_data_flat026_step : block004_data_flat026 = (CoefficientMerge.fastMerge block004_data_flat022 block004_data_flat025) := by decide +kernel
theorem block004_data_flat026_original : block004_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded))) := by
  rw [block004_data_flat026_step, block004_data_flat022_original, block004_data_flat025_original]
def block004_data_flat027 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440))]
theorem block004_data_flat027_step : block004_data_flat027 = (CoefficientMerge.fastMerge block004_data_flat021 block004_data_flat026) := by decide +kernel
theorem block004_data_flat027_original : block004_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) := by
  rw [block004_data_flat027_step, block004_data_flat021_original, block004_data_flat026_original]
def block004_data_flat028 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 130250160))]
theorem block004_data_flat028_step : block004_data_flat028 = (CoefficientMerge.scale (130250160 : Int) atom0328Coded) := by decide +kernel
theorem block004_data_flat028_original : block004_data_flat028 = (CoefficientMerge.scale (130250160 : Int) atom0328Coded) := by
  rw [block004_data_flat028_step]
def block004_data_flat029 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 47187840))]
theorem block004_data_flat029_step : block004_data_flat029 = (CoefficientMerge.scale (47187840 : Int) atom0329Coded) := by decide +kernel
theorem block004_data_flat029_original : block004_data_flat029 = (CoefficientMerge.scale (47187840 : Int) atom0329Coded) := by
  rw [block004_data_flat029_step]
def block004_data_flat030 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840))]
theorem block004_data_flat030_step : block004_data_flat030 = (CoefficientMerge.fastMerge block004_data_flat028 block004_data_flat029) := by decide +kernel
theorem block004_data_flat030_original : block004_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) := by
  rw [block004_data_flat030_step, block004_data_flat028_original, block004_data_flat029_original]
def block004_data_flat031 : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 89790720))]
theorem block004_data_flat031_step : block004_data_flat031 = (CoefficientMerge.scale (89790720 : Int) atom0330Coded) := by decide +kernel
theorem block004_data_flat031_original : block004_data_flat031 = (CoefficientMerge.scale (89790720 : Int) atom0330Coded) := by
  rw [block004_data_flat031_step]
def block004_data_flat032 : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 116319360))]
theorem block004_data_flat032_step : block004_data_flat032 = (CoefficientMerge.scale (116319360 : Int) atom0331Coded) := by decide +kernel
theorem block004_data_flat032_original : block004_data_flat032 = (CoefficientMerge.scale (116319360 : Int) atom0331Coded) := by
  rw [block004_data_flat032_step]
def block004_data_flat033 : CoefficientMerge.Poly := [(nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat033_step : block004_data_flat033 = (CoefficientMerge.scale (92273280 : Int) atom0332Coded) := by decide +kernel
theorem block004_data_flat033_original : block004_data_flat033 = (CoefficientMerge.scale (92273280 : Int) atom0332Coded) := by
  rw [block004_data_flat033_step]
def block004_data_flat034 : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat034_step : block004_data_flat034 = (CoefficientMerge.fastMerge block004_data_flat032 block004_data_flat033) := by decide +kernel
theorem block004_data_flat034_original : block004_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)) := by
  rw [block004_data_flat034_step, block004_data_flat032_original, block004_data_flat033_original]
def block004_data_flat035 : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat035_step : block004_data_flat035 = (CoefficientMerge.fastMerge block004_data_flat031 block004_data_flat034) := by decide +kernel
theorem block004_data_flat035_original : block004_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded))) := by
  rw [block004_data_flat035_step, block004_data_flat031_original, block004_data_flat034_original]
def block004_data_flat036 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat036_step : block004_data_flat036 = (CoefficientMerge.fastMerge block004_data_flat030 block004_data_flat035) := by decide +kernel
theorem block004_data_flat036_original : block004_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))) := by
  rw [block004_data_flat036_step, block004_data_flat030_original, block004_data_flat035_original]
def block004_data_flat037 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat037_step : block004_data_flat037 = (CoefficientMerge.fastMerge block004_data_flat027 block004_data_flat036) := by decide +kernel
theorem block004_data_flat037_original : block004_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded))))) := by
  rw [block004_data_flat037_step, block004_data_flat027_original, block004_data_flat036_original]
def block004_data_flat038 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920)), (nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280))]
theorem block004_data_flat038_step : block004_data_flat038 = (CoefficientMerge.fastMerge block004_data_flat018 block004_data_flat037) := by decide +kernel
theorem block004_data_flat038_original : block004_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))))) := by
  rw [block004_data_flat038_step, block004_data_flat018_original, block004_data_flat037_original]
def block004_data_flat039 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 112652640))]
theorem block004_data_flat039_step : block004_data_flat039 = (CoefficientMerge.scale (112652640 : Int) atom0333Coded) := by decide +kernel
theorem block004_data_flat039_original : block004_data_flat039 = (CoefficientMerge.scale (112652640 : Int) atom0333Coded) := by
  rw [block004_data_flat039_step]
def block004_data_flat040 : CoefficientMerge.Poly := [(nat_lit 567, Int.ofNat (nat_lit 106327680))]
theorem block004_data_flat040_step : block004_data_flat040 = (CoefficientMerge.scale (106327680 : Int) atom0334Coded) := by decide +kernel
theorem block004_data_flat040_original : block004_data_flat040 = (CoefficientMerge.scale (106327680 : Int) atom0334Coded) := by
  rw [block004_data_flat040_step]
def block004_data_flat041 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680))]
theorem block004_data_flat041_step : block004_data_flat041 = (CoefficientMerge.fastMerge block004_data_flat039 block004_data_flat040) := by decide +kernel
theorem block004_data_flat041_original : block004_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) := by
  rw [block004_data_flat041_step, block004_data_flat039_original, block004_data_flat040_original]
def block004_data_flat042 : CoefficientMerge.Poly := [(nat_lit 568, Int.ofNat (nat_lit 110265600))]
theorem block004_data_flat042_step : block004_data_flat042 = (CoefficientMerge.scale (110265600 : Int) atom0335Coded) := by decide +kernel
theorem block004_data_flat042_original : block004_data_flat042 = (CoefficientMerge.scale (110265600 : Int) atom0335Coded) := by
  rw [block004_data_flat042_step]
def block004_data_flat043 : CoefficientMerge.Poly := [(nat_lit 569, Int.ofNat (nat_lit 136537920))]
theorem block004_data_flat043_step : block004_data_flat043 = (CoefficientMerge.scale (136537920 : Int) atom0336Coded) := by decide +kernel
theorem block004_data_flat043_original : block004_data_flat043 = (CoefficientMerge.scale (136537920 : Int) atom0336Coded) := by
  rw [block004_data_flat043_step]
def block004_data_flat044 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 54432000))]
theorem block004_data_flat044_step : block004_data_flat044 = (CoefficientMerge.scale (54432000 : Int) atom0337Coded) := by decide +kernel
theorem block004_data_flat044_original : block004_data_flat044 = (CoefficientMerge.scale (54432000 : Int) atom0337Coded) := by
  rw [block004_data_flat044_step]
def block004_data_flat045 : CoefficientMerge.Poly := [(nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000))]
theorem block004_data_flat045_step : block004_data_flat045 = (CoefficientMerge.fastMerge block004_data_flat043 block004_data_flat044) := by decide +kernel
theorem block004_data_flat045_original : block004_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)) := by
  rw [block004_data_flat045_step, block004_data_flat043_original, block004_data_flat044_original]
def block004_data_flat046 : CoefficientMerge.Poly := [(nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000))]
theorem block004_data_flat046_step : block004_data_flat046 = (CoefficientMerge.fastMerge block004_data_flat042 block004_data_flat045) := by decide +kernel
theorem block004_data_flat046_original : block004_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded))) := by
  rw [block004_data_flat046_step, block004_data_flat042_original, block004_data_flat045_original]
def block004_data_flat047 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000))]
theorem block004_data_flat047_step : block004_data_flat047 = (CoefficientMerge.fastMerge block004_data_flat041 block004_data_flat046) := by decide +kernel
theorem block004_data_flat047_original : block004_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) := by
  rw [block004_data_flat047_step, block004_data_flat041_original, block004_data_flat046_original]
def block004_data_flat048 : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 131245920))]
theorem block004_data_flat048_step : block004_data_flat048 = (CoefficientMerge.scale (131245920 : Int) atom0338Coded) := by decide +kernel
theorem block004_data_flat048_original : block004_data_flat048 = (CoefficientMerge.scale (131245920 : Int) atom0338Coded) := by
  rw [block004_data_flat048_step]
def block004_data_flat049 : CoefficientMerge.Poly := [(nat_lit 580, Int.ofNat (nat_lit 102967200))]
theorem block004_data_flat049_step : block004_data_flat049 = (CoefficientMerge.scale (102967200 : Int) atom0339Coded) := by decide +kernel
theorem block004_data_flat049_original : block004_data_flat049 = (CoefficientMerge.scale (102967200 : Int) atom0339Coded) := by
  rw [block004_data_flat049_step]
def block004_data_flat050 : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200))]
theorem block004_data_flat050_step : block004_data_flat050 = (CoefficientMerge.fastMerge block004_data_flat048 block004_data_flat049) := by decide +kernel
theorem block004_data_flat050_original : block004_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) := by
  rw [block004_data_flat050_step, block004_data_flat048_original, block004_data_flat049_original]
def block004_data_flat051 : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 125612640))]
theorem block004_data_flat051_step : block004_data_flat051 = (CoefficientMerge.scale (125612640 : Int) atom0340Coded) := by decide +kernel
theorem block004_data_flat051_original : block004_data_flat051 = (CoefficientMerge.scale (125612640 : Int) atom0340Coded) := by
  rw [block004_data_flat051_step]
def block004_data_flat052 : CoefficientMerge.Poly := [(nat_lit 582, Int.ofNat (nat_lit 117365760))]
theorem block004_data_flat052_step : block004_data_flat052 = (CoefficientMerge.scale (117365760 : Int) atom0341Coded) := by decide +kernel
theorem block004_data_flat052_original : block004_data_flat052 = (CoefficientMerge.scale (117365760 : Int) atom0341Coded) := by
  rw [block004_data_flat052_step]
def block004_data_flat053 : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 107917920))]
theorem block004_data_flat053_step : block004_data_flat053 = (CoefficientMerge.scale (107917920 : Int) atom0342Coded) := by decide +kernel
theorem block004_data_flat053_original : block004_data_flat053 = (CoefficientMerge.scale (107917920 : Int) atom0342Coded) := by
  rw [block004_data_flat053_step]
def block004_data_flat054 : CoefficientMerge.Poly := [(nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920))]
theorem block004_data_flat054_step : block004_data_flat054 = (CoefficientMerge.fastMerge block004_data_flat052 block004_data_flat053) := by decide +kernel
theorem block004_data_flat054_original : block004_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded)) := by
  rw [block004_data_flat054_step, block004_data_flat052_original, block004_data_flat053_original]
def block004_data_flat055 : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920))]
theorem block004_data_flat055_step : block004_data_flat055 = (CoefficientMerge.fastMerge block004_data_flat051 block004_data_flat054) := by decide +kernel
theorem block004_data_flat055_original : block004_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))) := by
  rw [block004_data_flat055_step, block004_data_flat051_original, block004_data_flat054_original]
def block004_data_flat056 : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920))]
theorem block004_data_flat056_step : block004_data_flat056 = (CoefficientMerge.fastMerge block004_data_flat050 block004_data_flat055) := by decide +kernel
theorem block004_data_flat056_original : block004_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded)))) := by
  rw [block004_data_flat056_step, block004_data_flat050_original, block004_data_flat055_original]
def block004_data_flat057 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920))]
theorem block004_data_flat057_step : block004_data_flat057 = (CoefficientMerge.fastMerge block004_data_flat047 block004_data_flat056) := by decide +kernel
theorem block004_data_flat057_original : block004_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) := by
  rw [block004_data_flat057_step, block004_data_flat047_original, block004_data_flat056_original]
def block004_data_flat058 : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 160228800))]
theorem block004_data_flat058_step : block004_data_flat058 = (CoefficientMerge.scale (160228800 : Int) atom0343Coded) := by decide +kernel
theorem block004_data_flat058_original : block004_data_flat058 = (CoefficientMerge.scale (160228800 : Int) atom0343Coded) := by
  rw [block004_data_flat058_step]
def block004_data_flat059 : CoefficientMerge.Poly := [(nat_lit 594, Int.ofNat (nat_lit 90201600))]
theorem block004_data_flat059_step : block004_data_flat059 = (CoefficientMerge.scale (90201600 : Int) atom0344Coded) := by decide +kernel
theorem block004_data_flat059_original : block004_data_flat059 = (CoefficientMerge.scale (90201600 : Int) atom0344Coded) := by
  rw [block004_data_flat059_step]
def block004_data_flat060 : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600))]
theorem block004_data_flat060_step : block004_data_flat060 = (CoefficientMerge.fastMerge block004_data_flat058 block004_data_flat059) := by decide +kernel
theorem block004_data_flat060_original : block004_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) := by
  rw [block004_data_flat060_step, block004_data_flat058_original, block004_data_flat059_original]
def block004_data_flat061 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 146759040))]
theorem block004_data_flat061_step : block004_data_flat061 = (CoefficientMerge.scale (146759040 : Int) atom0345Coded) := by decide +kernel
theorem block004_data_flat061_original : block004_data_flat061 = (CoefficientMerge.scale (146759040 : Int) atom0345Coded) := by
  rw [block004_data_flat061_step]
def block004_data_flat062 : CoefficientMerge.Poly := [(nat_lit 596, Int.ofNat (nat_lit 193004640))]
theorem block004_data_flat062_step : block004_data_flat062 = (CoefficientMerge.scale (193004640 : Int) atom0346Coded) := by decide +kernel
theorem block004_data_flat062_original : block004_data_flat062 = (CoefficientMerge.scale (193004640 : Int) atom0346Coded) := by
  rw [block004_data_flat062_step]
def block004_data_flat063 : CoefficientMerge.Poly := [(nat_lit 597, Int.ofNat (nat_lit 188334720))]
theorem block004_data_flat063_step : block004_data_flat063 = (CoefficientMerge.scale (188334720 : Int) atom0347Coded) := by decide +kernel
theorem block004_data_flat063_original : block004_data_flat063 = (CoefficientMerge.scale (188334720 : Int) atom0347Coded) := by
  rw [block004_data_flat063_step]
def block004_data_flat064 : CoefficientMerge.Poly := [(nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720))]
theorem block004_data_flat064_step : block004_data_flat064 = (CoefficientMerge.fastMerge block004_data_flat062 block004_data_flat063) := by decide +kernel
theorem block004_data_flat064_original : block004_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)) := by
  rw [block004_data_flat064_step, block004_data_flat062_original, block004_data_flat063_original]
def block004_data_flat065 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720))]
theorem block004_data_flat065_step : block004_data_flat065 = (CoefficientMerge.fastMerge block004_data_flat061 block004_data_flat064) := by decide +kernel
theorem block004_data_flat065_original : block004_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded))) := by
  rw [block004_data_flat065_step, block004_data_flat061_original, block004_data_flat064_original]
def block004_data_flat066 : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720))]
theorem block004_data_flat066_step : block004_data_flat066 = (CoefficientMerge.fastMerge block004_data_flat060 block004_data_flat065) := by decide +kernel
theorem block004_data_flat066_original : block004_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) := by
  rw [block004_data_flat066_step, block004_data_flat060_original, block004_data_flat065_original]
def block004_data_flat067 : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 110393280))]
theorem block004_data_flat067_step : block004_data_flat067 = (CoefficientMerge.scale (110393280 : Int) atom0348Coded) := by decide +kernel
theorem block004_data_flat067_original : block004_data_flat067 = (CoefficientMerge.scale (110393280 : Int) atom0348Coded) := by
  rw [block004_data_flat067_step]
def block004_data_flat068 : CoefficientMerge.Poly := [(nat_lit 599, Int.ofNat (nat_lit 182864520))]
theorem block004_data_flat068_step : block004_data_flat068 = (CoefficientMerge.scale (182864520 : Int) atom0349Coded) := by decide +kernel
theorem block004_data_flat068_original : block004_data_flat068 = (CoefficientMerge.scale (182864520 : Int) atom0349Coded) := by
  rw [block004_data_flat068_step]
def block004_data_flat069 : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520))]
theorem block004_data_flat069_step : block004_data_flat069 = (CoefficientMerge.fastMerge block004_data_flat067 block004_data_flat068) := by decide +kernel
theorem block004_data_flat069_original : block004_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) := by
  rw [block004_data_flat069_step, block004_data_flat067_original, block004_data_flat068_original]
def block004_data_flat070 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 67526784))]
theorem block004_data_flat070_step : block004_data_flat070 = (CoefficientMerge.scale (67526784 : Int) atom0350Coded) := by decide +kernel
theorem block004_data_flat070_original : block004_data_flat070 = (CoefficientMerge.scale (67526784 : Int) atom0350Coded) := by
  rw [block004_data_flat070_step]
def block004_data_flat071 : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 158776200))]
theorem block004_data_flat071_step : block004_data_flat071 = (CoefficientMerge.scale (158776200 : Int) atom0351Coded) := by decide +kernel
theorem block004_data_flat071_original : block004_data_flat071 = (CoefficientMerge.scale (158776200 : Int) atom0351Coded) := by
  rw [block004_data_flat071_step]
def block004_data_flat072 : CoefficientMerge.Poly := [(nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat072_step : block004_data_flat072 = (CoefficientMerge.scale (177655680 : Int) atom0352Coded) := by decide +kernel
theorem block004_data_flat072_original : block004_data_flat072 = (CoefficientMerge.scale (177655680 : Int) atom0352Coded) := by
  rw [block004_data_flat072_step]
def block004_data_flat073 : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat073_step : block004_data_flat073 = (CoefficientMerge.fastMerge block004_data_flat071 block004_data_flat072) := by decide +kernel
theorem block004_data_flat073_original : block004_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded)) := by
  rw [block004_data_flat073_step, block004_data_flat071_original, block004_data_flat072_original]
def block004_data_flat074 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat074_step : block004_data_flat074 = (CoefficientMerge.fastMerge block004_data_flat070 block004_data_flat073) := by decide +kernel
theorem block004_data_flat074_original : block004_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))) := by
  rw [block004_data_flat074_step, block004_data_flat070_original, block004_data_flat073_original]
def block004_data_flat075 : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat075_step : block004_data_flat075 = (CoefficientMerge.fastMerge block004_data_flat069 block004_data_flat074) := by decide +kernel
theorem block004_data_flat075_original : block004_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded)))) := by
  rw [block004_data_flat075_step, block004_data_flat069_original, block004_data_flat074_original]
def block004_data_flat076 : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat076_step : block004_data_flat076 = (CoefficientMerge.fastMerge block004_data_flat066 block004_data_flat075) := by decide +kernel
theorem block004_data_flat076_original : block004_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))))) := by
  rw [block004_data_flat076_step, block004_data_flat066_original, block004_data_flat075_original]
def block004_data_flat077 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920)), (nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat077_step : block004_data_flat077 = (CoefficientMerge.fastMerge block004_data_flat057 block004_data_flat076) := by decide +kernel
theorem block004_data_flat077_original : block004_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded)))))) := by
  rw [block004_data_flat077_step, block004_data_flat057_original, block004_data_flat076_original]
def block004_data_flat078 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920)), (nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280)), (nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920)), (nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680))]
theorem block004_data_flat078_step : block004_data_flat078 = (CoefficientMerge.fastMerge block004_data_flat038 block004_data_flat077) := by decide +kernel
theorem block004_data_flat078_original : block004_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))))))) := by
  rw [block004_data_flat078_step, block004_data_flat038_original, block004_data_flat077_original]
def block004_data_flat079 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480))]
theorem block004_data_flat079_step : block004_data_flat079 = (CoefficientMerge.scale (120372480 : Int) atom0353Coded) := by decide +kernel
theorem block004_data_flat079_original : block004_data_flat079 = (CoefficientMerge.scale (120372480 : Int) atom0353Coded) := by
  rw [block004_data_flat079_step]
def block004_data_flat080 : CoefficientMerge.Poly := [(nat_lit 614, Int.ofNat (nat_lit 150013080))]
theorem block004_data_flat080_step : block004_data_flat080 = (CoefficientMerge.scale (150013080 : Int) atom0354Coded) := by decide +kernel
theorem block004_data_flat080_original : block004_data_flat080 = (CoefficientMerge.scale (150013080 : Int) atom0354Coded) := by
  rw [block004_data_flat080_step]
def block004_data_flat081 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080))]
theorem block004_data_flat081_step : block004_data_flat081 = (CoefficientMerge.fastMerge block004_data_flat079 block004_data_flat080) := by decide +kernel
theorem block004_data_flat081_original : block004_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) := by
  rw [block004_data_flat081_step, block004_data_flat079_original, block004_data_flat080_original]
def block004_data_flat082 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 102218760))]
theorem block004_data_flat082_step : block004_data_flat082 = (CoefficientMerge.scale (102218760 : Int) atom0355Coded) := by decide +kernel
theorem block004_data_flat082_original : block004_data_flat082 = (CoefficientMerge.scale (102218760 : Int) atom0355Coded) := by
  rw [block004_data_flat082_step]
def block004_data_flat083 : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 172461960))]
theorem block004_data_flat083_step : block004_data_flat083 = (CoefficientMerge.scale (172461960 : Int) atom0356Coded) := by decide +kernel
theorem block004_data_flat083_original : block004_data_flat083 = (CoefficientMerge.scale (172461960 : Int) atom0356Coded) := by
  rw [block004_data_flat083_step]
def block004_data_flat084 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 115864560))]
theorem block004_data_flat084_step : block004_data_flat084 = (CoefficientMerge.scale (115864560 : Int) atom0357Coded) := by decide +kernel
theorem block004_data_flat084_original : block004_data_flat084 = (CoefficientMerge.scale (115864560 : Int) atom0357Coded) := by
  rw [block004_data_flat084_step]
def block004_data_flat085 : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560))]
theorem block004_data_flat085_step : block004_data_flat085 = (CoefficientMerge.fastMerge block004_data_flat083 block004_data_flat084) := by decide +kernel
theorem block004_data_flat085_original : block004_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)) := by
  rw [block004_data_flat085_step, block004_data_flat083_original, block004_data_flat084_original]
def block004_data_flat086 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560))]
theorem block004_data_flat086_step : block004_data_flat086 = (CoefficientMerge.fastMerge block004_data_flat082 block004_data_flat085) := by decide +kernel
theorem block004_data_flat086_original : block004_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded))) := by
  rw [block004_data_flat086_step, block004_data_flat082_original, block004_data_flat085_original]
def block004_data_flat087 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560))]
theorem block004_data_flat087_step : block004_data_flat087 = (CoefficientMerge.fastMerge block004_data_flat081 block004_data_flat086) := by decide +kernel
theorem block004_data_flat087_original : block004_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) := by
  rw [block004_data_flat087_step, block004_data_flat081_original, block004_data_flat086_original]
def block004_data_flat088 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 154996200))]
theorem block004_data_flat088_step : block004_data_flat088 = (CoefficientMerge.scale (154996200 : Int) atom0358Coded) := by decide +kernel
theorem block004_data_flat088_original : block004_data_flat088 = (CoefficientMerge.scale (154996200 : Int) atom0358Coded) := by
  rw [block004_data_flat088_step]
def block004_data_flat089 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 64540800))]
theorem block004_data_flat089_step : block004_data_flat089 = (CoefficientMerge.scale (64540800 : Int) atom0359Coded) := by decide +kernel
theorem block004_data_flat089_original : block004_data_flat089 = (CoefficientMerge.scale (64540800 : Int) atom0359Coded) := by
  rw [block004_data_flat089_step]
def block004_data_flat090 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800))]
theorem block004_data_flat090_step : block004_data_flat090 = (CoefficientMerge.fastMerge block004_data_flat088 block004_data_flat089) := by decide +kernel
theorem block004_data_flat090_original : block004_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) := by
  rw [block004_data_flat090_step, block004_data_flat088_original, block004_data_flat089_original]
def block004_data_flat091 : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 90966240))]
theorem block004_data_flat091_step : block004_data_flat091 = (CoefficientMerge.scale (90966240 : Int) atom0360Coded) := by decide +kernel
theorem block004_data_flat091_original : block004_data_flat091 = (CoefficientMerge.scale (90966240 : Int) atom0360Coded) := by
  rw [block004_data_flat091_step]
def block004_data_flat092 : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 136631880))]
theorem block004_data_flat092_step : block004_data_flat092 = (CoefficientMerge.scale (136631880 : Int) atom0361Coded) := by decide +kernel
theorem block004_data_flat092_original : block004_data_flat092 = (CoefficientMerge.scale (136631880 : Int) atom0361Coded) := by
  rw [block004_data_flat092_step]
def block004_data_flat093 : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 15655680))]
theorem block004_data_flat093_step : block004_data_flat093 = (CoefficientMerge.scale (15655680 : Int) atom0362Coded) := by decide +kernel
theorem block004_data_flat093_original : block004_data_flat093 = (CoefficientMerge.scale (15655680 : Int) atom0362Coded) := by
  rw [block004_data_flat093_step]
def block004_data_flat094 : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680))]
theorem block004_data_flat094_step : block004_data_flat094 = (CoefficientMerge.fastMerge block004_data_flat092 block004_data_flat093) := by decide +kernel
theorem block004_data_flat094_original : block004_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded)) := by
  rw [block004_data_flat094_step, block004_data_flat092_original, block004_data_flat093_original]
def block004_data_flat095 : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680))]
theorem block004_data_flat095_step : block004_data_flat095 = (CoefficientMerge.fastMerge block004_data_flat091 block004_data_flat094) := by decide +kernel
theorem block004_data_flat095_original : block004_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))) := by
  rw [block004_data_flat095_step, block004_data_flat091_original, block004_data_flat094_original]
def block004_data_flat096 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680))]
theorem block004_data_flat096_step : block004_data_flat096 = (CoefficientMerge.fastMerge block004_data_flat090 block004_data_flat095) := by decide +kernel
theorem block004_data_flat096_original : block004_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded)))) := by
  rw [block004_data_flat096_step, block004_data_flat090_original, block004_data_flat095_original]
def block004_data_flat097 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680))]
theorem block004_data_flat097_step : block004_data_flat097 = (CoefficientMerge.fastMerge block004_data_flat087 block004_data_flat096) := by decide +kernel
theorem block004_data_flat097_original : block004_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) := by
  rw [block004_data_flat097_step, block004_data_flat087_original, block004_data_flat096_original]
def block004_data_flat098 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 78867000))]
theorem block004_data_flat098_step : block004_data_flat098 = (CoefficientMerge.scale (78867000 : Int) atom0363Coded) := by decide +kernel
theorem block004_data_flat098_original : block004_data_flat098 = (CoefficientMerge.scale (78867000 : Int) atom0363Coded) := by
  rw [block004_data_flat098_step]
def block004_data_flat099 : CoefficientMerge.Poly := [(nat_lit 674, Int.ofNat (nat_lit 55821960))]
theorem block004_data_flat099_step : block004_data_flat099 = (CoefficientMerge.scale (55821960 : Int) atom0364Coded) := by decide +kernel
theorem block004_data_flat099_original : block004_data_flat099 = (CoefficientMerge.scale (55821960 : Int) atom0364Coded) := by
  rw [block004_data_flat099_step]
def block004_data_flat100 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960))]
theorem block004_data_flat100_step : block004_data_flat100 = (CoefficientMerge.fastMerge block004_data_flat098 block004_data_flat099) := by decide +kernel
theorem block004_data_flat100_original : block004_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) := by
  rw [block004_data_flat100_step, block004_data_flat098_original, block004_data_flat099_original]
def block004_data_flat101 : CoefficientMerge.Poly := [(nat_lit 723, Int.ofNat (nat_lit 1382400))]
theorem block004_data_flat101_step : block004_data_flat101 = (CoefficientMerge.scale (1382400 : Int) atom0365Coded) := by decide +kernel
theorem block004_data_flat101_original : block004_data_flat101 = (CoefficientMerge.scale (1382400 : Int) atom0365Coded) := by
  rw [block004_data_flat101_step]
def block004_data_flat102 : CoefficientMerge.Poly := [(nat_lit 724, Int.ofNat (nat_lit 898560))]
theorem block004_data_flat102_step : block004_data_flat102 = (CoefficientMerge.scale (898560 : Int) atom0366Coded) := by decide +kernel
theorem block004_data_flat102_original : block004_data_flat102 = (CoefficientMerge.scale (898560 : Int) atom0366Coded) := by
  rw [block004_data_flat102_step]
def block004_data_flat103 : CoefficientMerge.Poly := [(nat_lit 725, Int.ofNat (nat_lit 449280))]
theorem block004_data_flat103_step : block004_data_flat103 = (CoefficientMerge.scale (449280 : Int) atom0367Coded) := by decide +kernel
theorem block004_data_flat103_original : block004_data_flat103 = (CoefficientMerge.scale (449280 : Int) atom0367Coded) := by
  rw [block004_data_flat103_step]
def block004_data_flat104 : CoefficientMerge.Poly := [(nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280))]
theorem block004_data_flat104_step : block004_data_flat104 = (CoefficientMerge.fastMerge block004_data_flat102 block004_data_flat103) := by decide +kernel
theorem block004_data_flat104_original : block004_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)) := by
  rw [block004_data_flat104_step, block004_data_flat102_original, block004_data_flat103_original]
def block004_data_flat105 : CoefficientMerge.Poly := [(nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280))]
theorem block004_data_flat105_step : block004_data_flat105 = (CoefficientMerge.fastMerge block004_data_flat101 block004_data_flat104) := by decide +kernel
theorem block004_data_flat105_original : block004_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded))) := by
  rw [block004_data_flat105_step, block004_data_flat101_original, block004_data_flat104_original]
def block004_data_flat106 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280))]
theorem block004_data_flat106_step : block004_data_flat106 = (CoefficientMerge.fastMerge block004_data_flat100 block004_data_flat105) := by decide +kernel
theorem block004_data_flat106_original : block004_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) := by
  rw [block004_data_flat106_step, block004_data_flat100_original, block004_data_flat105_original]
def block004_data_flat107 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 25693200))]
theorem block004_data_flat107_step : block004_data_flat107 = (CoefficientMerge.scale (25693200 : Int) atom0368Coded) := by decide +kernel
theorem block004_data_flat107_original : block004_data_flat107 = (CoefficientMerge.scale (25693200 : Int) atom0368Coded) := by
  rw [block004_data_flat107_step]
def block004_data_flat108 : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 9257760))]
theorem block004_data_flat108_step : block004_data_flat108 = (CoefficientMerge.scale (9257760 : Int) atom0369Coded) := by decide +kernel
theorem block004_data_flat108_original : block004_data_flat108 = (CoefficientMerge.scale (9257760 : Int) atom0369Coded) := by
  rw [block004_data_flat108_step]
def block004_data_flat109 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760))]
theorem block004_data_flat109_step : block004_data_flat109 = (CoefficientMerge.fastMerge block004_data_flat107 block004_data_flat108) := by decide +kernel
theorem block004_data_flat109_original : block004_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) := by
  rw [block004_data_flat109_step, block004_data_flat107_original, block004_data_flat108_original]
def block004_data_flat110 : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 4746240))]
theorem block004_data_flat110_step : block004_data_flat110 = (CoefficientMerge.scale (4746240 : Int) atom0370Coded) := by decide +kernel
theorem block004_data_flat110_original : block004_data_flat110 = (CoefficientMerge.scale (4746240 : Int) atom0370Coded) := by
  rw [block004_data_flat110_step]
def block004_data_flat111 : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 2148480))]
theorem block004_data_flat111_step : block004_data_flat111 = (CoefficientMerge.scale (2148480 : Int) atom0371Coded) := by decide +kernel
theorem block004_data_flat111_original : block004_data_flat111 = (CoefficientMerge.scale (2148480 : Int) atom0371Coded) := by
  rw [block004_data_flat111_step]
def block004_data_flat112 : CoefficientMerge.Poly := [(nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat112_step : block004_data_flat112 = (CoefficientMerge.scale (3600000 : Int) atom0372Coded) := by decide +kernel
theorem block004_data_flat112_original : block004_data_flat112 = (CoefficientMerge.scale (3600000 : Int) atom0372Coded) := by
  rw [block004_data_flat112_step]
def block004_data_flat113 : CoefficientMerge.Poly := [(nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat113_step : block004_data_flat113 = (CoefficientMerge.fastMerge block004_data_flat111 block004_data_flat112) := by decide +kernel
theorem block004_data_flat113_original : block004_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)) := by
  rw [block004_data_flat113_step, block004_data_flat111_original, block004_data_flat112_original]
def block004_data_flat114 : CoefficientMerge.Poly := [(nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat114_step : block004_data_flat114 = (CoefficientMerge.fastMerge block004_data_flat110 block004_data_flat113) := by decide +kernel
theorem block004_data_flat114_original : block004_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded))) := by
  rw [block004_data_flat114_step, block004_data_flat110_original, block004_data_flat113_original]
def block004_data_flat115 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat115_step : block004_data_flat115 = (CoefficientMerge.fastMerge block004_data_flat109 block004_data_flat114) := by decide +kernel
theorem block004_data_flat115_original : block004_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))) := by
  rw [block004_data_flat115_step, block004_data_flat109_original, block004_data_flat114_original]
def block004_data_flat116 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat116_step : block004_data_flat116 = (CoefficientMerge.fastMerge block004_data_flat106 block004_data_flat115) := by decide +kernel
theorem block004_data_flat116_original : block004_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded))))) := by
  rw [block004_data_flat116_step, block004_data_flat106_original, block004_data_flat115_original]
def block004_data_flat117 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680)), (nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000))]
theorem block004_data_flat117_step : block004_data_flat117 = (CoefficientMerge.fastMerge block004_data_flat097 block004_data_flat116) := by decide +kernel
theorem block004_data_flat117_original : block004_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))))) := by
  rw [block004_data_flat117_step, block004_data_flat097_original, block004_data_flat116_original]
def block004_data_flat118 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 5500800))]
theorem block004_data_flat118_step : block004_data_flat118 = (CoefficientMerge.scale (5500800 : Int) atom0373Coded) := by decide +kernel
theorem block004_data_flat118_original : block004_data_flat118 = (CoefficientMerge.scale (5500800 : Int) atom0373Coded) := by
  rw [block004_data_flat118_step]
def block004_data_flat119 : CoefficientMerge.Poly := [(nat_lit 743, Int.ofNat (nat_lit 7401600))]
theorem block004_data_flat119_step : block004_data_flat119 = (CoefficientMerge.scale (7401600 : Int) atom0374Coded) := by decide +kernel
theorem block004_data_flat119_original : block004_data_flat119 = (CoefficientMerge.scale (7401600 : Int) atom0374Coded) := by
  rw [block004_data_flat119_step]
def block004_data_flat120 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600))]
theorem block004_data_flat120_step : block004_data_flat120 = (CoefficientMerge.fastMerge block004_data_flat118 block004_data_flat119) := by decide +kernel
theorem block004_data_flat120_original : block004_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) := by
  rw [block004_data_flat120_step, block004_data_flat118_original, block004_data_flat119_original]
def block004_data_flat121 : CoefficientMerge.Poly := [(nat_lit 744, Int.ofNat (nat_lit 56678400))]
theorem block004_data_flat121_step : block004_data_flat121 = (CoefficientMerge.scale (56678400 : Int) atom0375Coded) := by decide +kernel
theorem block004_data_flat121_original : block004_data_flat121 = (CoefficientMerge.scale (56678400 : Int) atom0375Coded) := by
  rw [block004_data_flat121_step]
def block004_data_flat122 : CoefficientMerge.Poly := [(nat_lit 745, Int.ofNat (nat_lit 16715520))]
theorem block004_data_flat122_step : block004_data_flat122 = (CoefficientMerge.scale (16715520 : Int) atom0376Coded) := by decide +kernel
theorem block004_data_flat122_original : block004_data_flat122 = (CoefficientMerge.scale (16715520 : Int) atom0376Coded) := by
  rw [block004_data_flat122_step]
def block004_data_flat123 : CoefficientMerge.Poly := [(nat_lit 746, Int.ofNat (nat_lit 35445600))]
theorem block004_data_flat123_step : block004_data_flat123 = (CoefficientMerge.scale (35445600 : Int) atom0377Coded) := by decide +kernel
theorem block004_data_flat123_original : block004_data_flat123 = (CoefficientMerge.scale (35445600 : Int) atom0377Coded) := by
  rw [block004_data_flat123_step]
def block004_data_flat124 : CoefficientMerge.Poly := [(nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600))]
theorem block004_data_flat124_step : block004_data_flat124 = (CoefficientMerge.fastMerge block004_data_flat122 block004_data_flat123) := by decide +kernel
theorem block004_data_flat124_original : block004_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)) := by
  rw [block004_data_flat124_step, block004_data_flat122_original, block004_data_flat123_original]
def block004_data_flat125 : CoefficientMerge.Poly := [(nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600))]
theorem block004_data_flat125_step : block004_data_flat125 = (CoefficientMerge.fastMerge block004_data_flat121 block004_data_flat124) := by decide +kernel
theorem block004_data_flat125_original : block004_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded))) := by
  rw [block004_data_flat125_step, block004_data_flat121_original, block004_data_flat124_original]
def block004_data_flat126 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600))]
theorem block004_data_flat126_step : block004_data_flat126 = (CoefficientMerge.fastMerge block004_data_flat120 block004_data_flat125) := by decide +kernel
theorem block004_data_flat126_original : block004_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) := by
  rw [block004_data_flat126_step, block004_data_flat120_original, block004_data_flat125_original]
def block004_data_flat127 : CoefficientMerge.Poly := [(nat_lit 747, Int.ofNat (nat_lit 31541760))]
theorem block004_data_flat127_step : block004_data_flat127 = (CoefficientMerge.scale (31541760 : Int) atom0378Coded) := by decide +kernel
theorem block004_data_flat127_original : block004_data_flat127 = (CoefficientMerge.scale (31541760 : Int) atom0378Coded) := by
  rw [block004_data_flat127_step]
def block004_data_flat128 : CoefficientMerge.Poly := [(nat_lit 748, Int.ofNat (nat_lit 40792320))]
theorem block004_data_flat128_step : block004_data_flat128 = (CoefficientMerge.scale (40792320 : Int) atom0379Coded) := by decide +kernel
theorem block004_data_flat128_original : block004_data_flat128 = (CoefficientMerge.scale (40792320 : Int) atom0379Coded) := by
  rw [block004_data_flat128_step]
def block004_data_flat129 : CoefficientMerge.Poly := [(nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320))]
theorem block004_data_flat129_step : block004_data_flat129 = (CoefficientMerge.fastMerge block004_data_flat127 block004_data_flat128) := by decide +kernel
theorem block004_data_flat129_original : block004_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) := by
  rw [block004_data_flat129_step, block004_data_flat127_original, block004_data_flat128_original]
def block004_data_flat130 : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 50042880))]
theorem block004_data_flat130_step : block004_data_flat130 = (CoefficientMerge.scale (50042880 : Int) atom0380Coded) := by decide +kernel
theorem block004_data_flat130_original : block004_data_flat130 = (CoefficientMerge.scale (50042880 : Int) atom0380Coded) := by
  rw [block004_data_flat130_step]
def block004_data_flat131 : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 8098560))]
theorem block004_data_flat131_step : block004_data_flat131 = (CoefficientMerge.scale (8098560 : Int) atom0381Coded) := by decide +kernel
theorem block004_data_flat131_original : block004_data_flat131 = (CoefficientMerge.scale (8098560 : Int) atom0381Coded) := by
  rw [block004_data_flat131_step]
def block004_data_flat132 : CoefficientMerge.Poly := [(nat_lit 756, Int.ofNat (nat_lit 16456320))]
theorem block004_data_flat132_step : block004_data_flat132 = (CoefficientMerge.scale (16456320 : Int) atom0382Coded) := by decide +kernel
theorem block004_data_flat132_original : block004_data_flat132 = (CoefficientMerge.scale (16456320 : Int) atom0382Coded) := by
  rw [block004_data_flat132_step]
def block004_data_flat133 : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320))]
theorem block004_data_flat133_step : block004_data_flat133 = (CoefficientMerge.fastMerge block004_data_flat131 block004_data_flat132) := by decide +kernel
theorem block004_data_flat133_original : block004_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded)) := by
  rw [block004_data_flat133_step, block004_data_flat131_original, block004_data_flat132_original]
def block004_data_flat134 : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320))]
theorem block004_data_flat134_step : block004_data_flat134 = (CoefficientMerge.fastMerge block004_data_flat130 block004_data_flat133) := by decide +kernel
theorem block004_data_flat134_original : block004_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))) := by
  rw [block004_data_flat134_step, block004_data_flat130_original, block004_data_flat133_original]
def block004_data_flat135 : CoefficientMerge.Poly := [(nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320))]
theorem block004_data_flat135_step : block004_data_flat135 = (CoefficientMerge.fastMerge block004_data_flat129 block004_data_flat134) := by decide +kernel
theorem block004_data_flat135_original : block004_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded)))) := by
  rw [block004_data_flat135_step, block004_data_flat129_original, block004_data_flat134_original]
def block004_data_flat136 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320))]
theorem block004_data_flat136_step : block004_data_flat136 = (CoefficientMerge.fastMerge block004_data_flat126 block004_data_flat135) := by decide +kernel
theorem block004_data_flat136_original : block004_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) := by
  rw [block004_data_flat136_step, block004_data_flat126_original, block004_data_flat135_original]
def block004_data_flat137 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 19065600))]
theorem block004_data_flat137_step : block004_data_flat137 = (CoefficientMerge.scale (19065600 : Int) atom0383Coded) := by decide +kernel
theorem block004_data_flat137_original : block004_data_flat137 = (CoefficientMerge.scale (19065600 : Int) atom0383Coded) := by
  rw [block004_data_flat137_step]
def block004_data_flat138 : CoefficientMerge.Poly := [(nat_lit 758, Int.ofNat (nat_lit 21674880))]
theorem block004_data_flat138_step : block004_data_flat138 = (CoefficientMerge.scale (21674880 : Int) atom0384Coded) := by decide +kernel
theorem block004_data_flat138_original : block004_data_flat138 = (CoefficientMerge.scale (21674880 : Int) atom0384Coded) := by
  rw [block004_data_flat138_step]
def block004_data_flat139 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880))]
theorem block004_data_flat139_step : block004_data_flat139 = (CoefficientMerge.fastMerge block004_data_flat137 block004_data_flat138) := by decide +kernel
theorem block004_data_flat139_original : block004_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) := by
  rw [block004_data_flat139_step, block004_data_flat137_original, block004_data_flat138_original]
def block004_data_flat140 : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 64419840))]
theorem block004_data_flat140_step : block004_data_flat140 = (CoefficientMerge.scale (64419840 : Int) atom0385Coded) := by decide +kernel
theorem block004_data_flat140_original : block004_data_flat140 = (CoefficientMerge.scale (64419840 : Int) atom0385Coded) := by
  rw [block004_data_flat140_step]
def block004_data_flat141 : CoefficientMerge.Poly := [(nat_lit 760, Int.ofNat (nat_lit 35062560))]
theorem block004_data_flat141_step : block004_data_flat141 = (CoefficientMerge.scale (35062560 : Int) atom0386Coded) := by decide +kernel
theorem block004_data_flat141_original : block004_data_flat141 = (CoefficientMerge.scale (35062560 : Int) atom0386Coded) := by
  rw [block004_data_flat141_step]
def block004_data_flat142 : CoefficientMerge.Poly := [(nat_lit 761, Int.ofNat (nat_lit 52725600))]
theorem block004_data_flat142_step : block004_data_flat142 = (CoefficientMerge.scale (52725600 : Int) atom0387Coded) := by decide +kernel
theorem block004_data_flat142_original : block004_data_flat142 = (CoefficientMerge.scale (52725600 : Int) atom0387Coded) := by
  rw [block004_data_flat142_step]
def block004_data_flat143 : CoefficientMerge.Poly := [(nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600))]
theorem block004_data_flat143_step : block004_data_flat143 = (CoefficientMerge.fastMerge block004_data_flat141 block004_data_flat142) := by decide +kernel
theorem block004_data_flat143_original : block004_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)) := by
  rw [block004_data_flat143_step, block004_data_flat141_original, block004_data_flat142_original]
def block004_data_flat144 : CoefficientMerge.Poly := [(nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600))]
theorem block004_data_flat144_step : block004_data_flat144 = (CoefficientMerge.fastMerge block004_data_flat140 block004_data_flat143) := by decide +kernel
theorem block004_data_flat144_original : block004_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded))) := by
  rw [block004_data_flat144_step, block004_data_flat140_original, block004_data_flat143_original]
def block004_data_flat145 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600))]
theorem block004_data_flat145_step : block004_data_flat145 = (CoefficientMerge.fastMerge block004_data_flat139 block004_data_flat144) := by decide +kernel
theorem block004_data_flat145_original : block004_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) := by
  rw [block004_data_flat145_step, block004_data_flat139_original, block004_data_flat144_original]
def block004_data_flat146 : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 56619360))]
theorem block004_data_flat146_step : block004_data_flat146 = (CoefficientMerge.scale (56619360 : Int) atom0388Coded) := by decide +kernel
theorem block004_data_flat146_original : block004_data_flat146 = (CoefficientMerge.scale (56619360 : Int) atom0388Coded) := by
  rw [block004_data_flat146_step]
def block004_data_flat147 : CoefficientMerge.Poly := [(nat_lit 763, Int.ofNat (nat_lit 70120800))]
theorem block004_data_flat147_step : block004_data_flat147 = (CoefficientMerge.scale (70120800 : Int) atom0389Coded) := by decide +kernel
theorem block004_data_flat147_original : block004_data_flat147 = (CoefficientMerge.scale (70120800 : Int) atom0389Coded) := by
  rw [block004_data_flat147_step]
def block004_data_flat148 : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800))]
theorem block004_data_flat148_step : block004_data_flat148 = (CoefficientMerge.fastMerge block004_data_flat146 block004_data_flat147) := by decide +kernel
theorem block004_data_flat148_original : block004_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) := by
  rw [block004_data_flat148_step, block004_data_flat146_original, block004_data_flat147_original]
def block004_data_flat149 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 83622240))]
theorem block004_data_flat149_step : block004_data_flat149 = (CoefficientMerge.scale (83622240 : Int) atom0390Coded) := by decide +kernel
theorem block004_data_flat149_original : block004_data_flat149 = (CoefficientMerge.scale (83622240 : Int) atom0390Coded) := by
  rw [block004_data_flat149_step]
def block004_data_flat150 : CoefficientMerge.Poly := [(nat_lit 771, Int.ofNat (nat_lit 15724800))]
theorem block004_data_flat150_step : block004_data_flat150 = (CoefficientMerge.scale (15724800 : Int) atom0391Coded) := by decide +kernel
theorem block004_data_flat150_original : block004_data_flat150 = (CoefficientMerge.scale (15724800 : Int) atom0391Coded) := by
  rw [block004_data_flat150_step]
def block004_data_flat151 : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat151_step : block004_data_flat151 = (CoefficientMerge.scale (33575040 : Int) atom0392Coded) := by decide +kernel
theorem block004_data_flat151_original : block004_data_flat151 = (CoefficientMerge.scale (33575040 : Int) atom0392Coded) := by
  rw [block004_data_flat151_step]
def block004_data_flat152 : CoefficientMerge.Poly := [(nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat152_step : block004_data_flat152 = (CoefficientMerge.fastMerge block004_data_flat150 block004_data_flat151) := by decide +kernel
theorem block004_data_flat152_original : block004_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded)) := by
  rw [block004_data_flat152_step, block004_data_flat150_original, block004_data_flat151_original]
def block004_data_flat153 : CoefficientMerge.Poly := [(nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat153_step : block004_data_flat153 = (CoefficientMerge.fastMerge block004_data_flat149 block004_data_flat152) := by decide +kernel
theorem block004_data_flat153_original : block004_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded))) := by
  rw [block004_data_flat153_step, block004_data_flat149_original, block004_data_flat152_original]
def block004_data_flat154 : CoefficientMerge.Poly := [(nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat154_step : block004_data_flat154 = (CoefficientMerge.fastMerge block004_data_flat148 block004_data_flat153) := by decide +kernel
theorem block004_data_flat154_original : block004_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded)))) := by
  rw [block004_data_flat154_step, block004_data_flat148_original, block004_data_flat153_original]
def block004_data_flat155 : CoefficientMerge.Poly := [(nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat155_step : block004_data_flat155 = (CoefficientMerge.fastMerge block004_data_flat145 block004_data_flat154) := by decide +kernel
theorem block004_data_flat155_original : block004_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded))))) := by
  rw [block004_data_flat155_step, block004_data_flat145_original, block004_data_flat154_original]
def block004_data_flat156 : CoefficientMerge.Poly := [(nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320)), (nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat156_step : block004_data_flat156 = (CoefficientMerge.fastMerge block004_data_flat136 block004_data_flat155) := by decide +kernel
theorem block004_data_flat156_original : block004_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded)))))) := by
  rw [block004_data_flat156_step, block004_data_flat136_original, block004_data_flat155_original]
def block004_data_flat157 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680)), (nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000)), (nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320)), (nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat157_step : block004_data_flat157 = (CoefficientMerge.fastMerge block004_data_flat117 block004_data_flat156) := by decide +kernel
theorem block004_data_flat157_original : block004_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded))))))) := by
  rw [block004_data_flat157_step, block004_data_flat117_original, block004_data_flat156_original]
def block004_data_flat158 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920)), (nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280)), (nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920)), (nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680)), (nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680)), (nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000)), (nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320)), (nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat158_step : block004_data_flat158 = (CoefficientMerge.fastMerge block004_data_flat078 block004_data_flat157) := by decide +kernel
theorem block004_data_flat158_original : block004_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded)))))))) := by
  rw [block004_data_flat158_step, block004_data_flat078_original, block004_data_flat157_original]
def block004_data_flat159 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 61263360)), (nat_lit 534, Int.ofNat (nat_lit 102746880)), (nat_lit 535, Int.ofNat (nat_lit 68907600)), (nat_lit 536, Int.ofNat (nat_lit 86732640)), (nat_lit 537, Int.ofNat (nat_lit 84196080)), (nat_lit 538, Int.ofNat (nat_lit 87441840)), (nat_lit 539, Int.ofNat (nat_lit 113022000)), (nat_lit 546, Int.ofNat (nat_lit 38949120)), (nat_lit 547, Int.ofNat (nat_lit 76222080)), (nat_lit 548, Int.ofNat (nat_lit 74545920)), (nat_lit 549, Int.ofNat (nat_lit 108552960)), (nat_lit 550, Int.ofNat (nat_lit 81308880)), (nat_lit 551, Int.ofNat (nat_lit 99692640)), (nat_lit 552, Int.ofNat (nat_lit 98187120)), (nat_lit 553, Int.ofNat (nat_lit 103051440)), (nat_lit 554, Int.ofNat (nat_lit 130250160)), (nat_lit 562, Int.ofNat (nat_lit 47187840)), (nat_lit 563, Int.ofNat (nat_lit 89790720)), (nat_lit 564, Int.ofNat (nat_lit 116319360)), (nat_lit 565, Int.ofNat (nat_lit 92273280)), (nat_lit 566, Int.ofNat (nat_lit 112652640)), (nat_lit 567, Int.ofNat (nat_lit 106327680)), (nat_lit 568, Int.ofNat (nat_lit 110265600)), (nat_lit 569, Int.ofNat (nat_lit 136537920)), (nat_lit 578, Int.ofNat (nat_lit 54432000)), (nat_lit 579, Int.ofNat (nat_lit 131245920)), (nat_lit 580, Int.ofNat (nat_lit 102967200)), (nat_lit 581, Int.ofNat (nat_lit 125612640)), (nat_lit 582, Int.ofNat (nat_lit 117365760)), (nat_lit 583, Int.ofNat (nat_lit 107917920)), (nat_lit 584, Int.ofNat (nat_lit 160228800)), (nat_lit 594, Int.ofNat (nat_lit 90201600)), (nat_lit 595, Int.ofNat (nat_lit 146759040)), (nat_lit 596, Int.ofNat (nat_lit 193004640)), (nat_lit 597, Int.ofNat (nat_lit 188334720)), (nat_lit 598, Int.ofNat (nat_lit 110393280)), (nat_lit 599, Int.ofNat (nat_lit 182864520)), (nat_lit 610, Int.ofNat (nat_lit 67526784)), (nat_lit 611, Int.ofNat (nat_lit 158776200)), (nat_lit 612, Int.ofNat (nat_lit 177655680)), (nat_lit 613, Int.ofNat (nat_lit 120372480)), (nat_lit 614, Int.ofNat (nat_lit 150013080)), (nat_lit 626, Int.ofNat (nat_lit 102218760)), (nat_lit 627, Int.ofNat (nat_lit 172461960)), (nat_lit 628, Int.ofNat (nat_lit 115864560)), (nat_lit 629, Int.ofNat (nat_lit 154996200)), (nat_lit 642, Int.ofNat (nat_lit 64540800)), (nat_lit 643, Int.ofNat (nat_lit 90966240)), (nat_lit 644, Int.ofNat (nat_lit 136631880)), (nat_lit 658, Int.ofNat (nat_lit 15655680)), (nat_lit 659, Int.ofNat (nat_lit 78867000)), (nat_lit 674, Int.ofNat (nat_lit 55821960)), (nat_lit 723, Int.ofNat (nat_lit 1382400)), (nat_lit 724, Int.ofNat (nat_lit 898560)), (nat_lit 725, Int.ofNat (nat_lit 449280)), (nat_lit 729, Int.ofNat (nat_lit 25693200)), (nat_lit 731, Int.ofNat (nat_lit 9257760)), (nat_lit 739, Int.ofNat (nat_lit 4746240)), (nat_lit 740, Int.ofNat (nat_lit 2148480)), (nat_lit 741, Int.ofNat (nat_lit 3600000)), (nat_lit 742, Int.ofNat (nat_lit 5500800)), (nat_lit 743, Int.ofNat (nat_lit 7401600)), (nat_lit 744, Int.ofNat (nat_lit 56678400)), (nat_lit 745, Int.ofNat (nat_lit 16715520)), (nat_lit 746, Int.ofNat (nat_lit 35445600)), (nat_lit 747, Int.ofNat (nat_lit 31541760)), (nat_lit 748, Int.ofNat (nat_lit 40792320)), (nat_lit 749, Int.ofNat (nat_lit 50042880)), (nat_lit 755, Int.ofNat (nat_lit 8098560)), (nat_lit 756, Int.ofNat (nat_lit 16456320)), (nat_lit 757, Int.ofNat (nat_lit 19065600)), (nat_lit 758, Int.ofNat (nat_lit 21674880)), (nat_lit 759, Int.ofNat (nat_lit 64419840)), (nat_lit 760, Int.ofNat (nat_lit 35062560)), (nat_lit 761, Int.ofNat (nat_lit 52725600)), (nat_lit 762, Int.ofNat (nat_lit 56619360)), (nat_lit 763, Int.ofNat (nat_lit 70120800)), (nat_lit 764, Int.ofNat (nat_lit 83622240)), (nat_lit 771, Int.ofNat (nat_lit 15724800)), (nat_lit 772, Int.ofNat (nat_lit 33575040))]
theorem block004_data_flat159_step : block004_data_flat159 = (CoefficientMerge.trim block004_data_flat158) := by decide +kernel
theorem block004_data_flat159_original : block004_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded))))))))) := by
  rw [block004_data_flat159_step, block004_data_flat158_original]
theorem block004_data : block004 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0313Coded) (CoefficientMerge.scale (102746880 : Int) atom0314Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68907600 : Int) atom0315Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86732640 : Int) atom0316Coded) (CoefficientMerge.scale (84196080 : Int) atom0317Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87441840 : Int) atom0318Coded) (CoefficientMerge.scale (113022000 : Int) atom0319Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38949120 : Int) atom0320Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76222080 : Int) atom0321Coded) (CoefficientMerge.scale (74545920 : Int) atom0322Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108552960 : Int) atom0323Coded) (CoefficientMerge.scale (81308880 : Int) atom0324Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99692640 : Int) atom0325Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98187120 : Int) atom0326Coded) (CoefficientMerge.scale (103051440 : Int) atom0327Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130250160 : Int) atom0328Coded) (CoefficientMerge.scale (47187840 : Int) atom0329Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89790720 : Int) atom0330Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116319360 : Int) atom0331Coded) (CoefficientMerge.scale (92273280 : Int) atom0332Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112652640 : Int) atom0333Coded) (CoefficientMerge.scale (106327680 : Int) atom0334Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110265600 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136537920 : Int) atom0336Coded) (CoefficientMerge.scale (54432000 : Int) atom0337Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131245920 : Int) atom0338Coded) (CoefficientMerge.scale (102967200 : Int) atom0339Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125612640 : Int) atom0340Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117365760 : Int) atom0341Coded) (CoefficientMerge.scale (107917920 : Int) atom0342Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (160228800 : Int) atom0343Coded) (CoefficientMerge.scale (90201600 : Int) atom0344Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146759040 : Int) atom0345Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193004640 : Int) atom0346Coded) (CoefficientMerge.scale (188334720 : Int) atom0347Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110393280 : Int) atom0348Coded) (CoefficientMerge.scale (182864520 : Int) atom0349Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67526784 : Int) atom0350Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158776200 : Int) atom0351Coded) (CoefficientMerge.scale (177655680 : Int) atom0352Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120372480 : Int) atom0353Coded) (CoefficientMerge.scale (150013080 : Int) atom0354Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218760 : Int) atom0355Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172461960 : Int) atom0356Coded) (CoefficientMerge.scale (115864560 : Int) atom0357Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (154996200 : Int) atom0358Coded) (CoefficientMerge.scale (64540800 : Int) atom0359Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90966240 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136631880 : Int) atom0361Coded) (CoefficientMerge.scale (15655680 : Int) atom0362Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78867000 : Int) atom0363Coded) (CoefficientMerge.scale (55821960 : Int) atom0364Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1382400 : Int) atom0365Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (898560 : Int) atom0366Coded) (CoefficientMerge.scale (449280 : Int) atom0367Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25693200 : Int) atom0368Coded) (CoefficientMerge.scale (9257760 : Int) atom0369Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4746240 : Int) atom0370Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148480 : Int) atom0371Coded) (CoefficientMerge.scale (3600000 : Int) atom0372Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5500800 : Int) atom0373Coded) (CoefficientMerge.scale (7401600 : Int) atom0374Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56678400 : Int) atom0375Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16715520 : Int) atom0376Coded) (CoefficientMerge.scale (35445600 : Int) atom0377Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31541760 : Int) atom0378Coded) (CoefficientMerge.scale (40792320 : Int) atom0379Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50042880 : Int) atom0380Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8098560 : Int) atom0381Coded) (CoefficientMerge.scale (16456320 : Int) atom0382Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19065600 : Int) atom0383Coded) (CoefficientMerge.scale (21674880 : Int) atom0384Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64419840 : Int) atom0385Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35062560 : Int) atom0386Coded) (CoefficientMerge.scale (52725600 : Int) atom0387Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56619360 : Int) atom0388Coded) (CoefficientMerge.scale (70120800 : Int) atom0389Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83622240 : Int) atom0390Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15724800 : Int) atom0391Coded) (CoefficientMerge.scale (33575040 : Int) atom0392Coded)))))))) := by
  have h : block004 = block004_data_flat159 := by decide +kernel
  exact h.trans block004_data_flat159_original
theorem block004_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block004 := by
  rw [block004_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0313Coded_nonneg g hg hA hB) (atom0314Coded_nonneg g hg hA hB)) (add_nonneg (atom0315Coded_nonneg g hg hA hB) (add_nonneg (atom0316Coded_nonneg g hg hA hB) (atom0317Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0318Coded_nonneg g hg hA hB) (atom0319Coded_nonneg g hg hA hB)) (add_nonneg (atom0320Coded_nonneg g hg hA hB) (add_nonneg (atom0321Coded_nonneg g hg hA hB) (atom0322Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0323Coded_nonneg g hg hA hB) (atom0324Coded_nonneg g hg hA hB)) (add_nonneg (atom0325Coded_nonneg g hg hA hB) (add_nonneg (atom0326Coded_nonneg g hg hA hB) (atom0327Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0328Coded_nonneg g hg hA hB) (atom0329Coded_nonneg g hg hA hB)) (add_nonneg (atom0330Coded_nonneg g hg hA hB) (add_nonneg (atom0331Coded_nonneg g hg hA hB) (atom0332Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0333Coded_nonneg g hg hA hB) (atom0334Coded_nonneg g hg hA hB)) (add_nonneg (atom0335Coded_nonneg g hg hA hB) (add_nonneg (atom0336Coded_nonneg g hg hA hB) (atom0337Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0338Coded_nonneg g hg hA hB) (atom0339Coded_nonneg g hg hA hB)) (add_nonneg (atom0340Coded_nonneg g hg hA hB) (add_nonneg (atom0341Coded_nonneg g hg hA hB) (atom0342Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0343Coded_nonneg g hg hA hB) (atom0344Coded_nonneg g hg hA hB)) (add_nonneg (atom0345Coded_nonneg g hg hA hB) (add_nonneg (atom0346Coded_nonneg g hg hA hB) (atom0347Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0348Coded_nonneg g hg hA hB) (atom0349Coded_nonneg g hg hA hB)) (add_nonneg (atom0350Coded_nonneg g hg hA hB) (add_nonneg (atom0351Coded_nonneg g hg hA hB) (atom0352Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0353Coded_nonneg g hg hA hB) (atom0354Coded_nonneg g hg hA hB)) (add_nonneg (atom0355Coded_nonneg g hg hA hB) (add_nonneg (atom0356Coded_nonneg g hg hA hB) (atom0357Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0358Coded_nonneg g hg hA hB) (atom0359Coded_nonneg g hg hA hB)) (add_nonneg (atom0360Coded_nonneg g hg hA hB) (add_nonneg (atom0361Coded_nonneg g hg hA hB) (atom0362Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0363Coded_nonneg g hg hA hB) (atom0364Coded_nonneg g hg hA hB)) (add_nonneg (atom0365Coded_nonneg g hg hA hB) (add_nonneg (atom0366Coded_nonneg g hg hA hB) (atom0367Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0368Coded_nonneg g hg hA hB) (atom0369Coded_nonneg g hg hA hB)) (add_nonneg (atom0370Coded_nonneg g hg hA hB) (add_nonneg (atom0371Coded_nonneg g hg hA hB) (atom0372Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0373Coded_nonneg g hg hA hB) (atom0374Coded_nonneg g hg hA hB)) (add_nonneg (atom0375Coded_nonneg g hg hA hB) (add_nonneg (atom0376Coded_nonneg g hg hA hB) (atom0377Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0378Coded_nonneg g hg hA hB) (atom0379Coded_nonneg g hg hA hB)) (add_nonneg (atom0380Coded_nonneg g hg hA hB) (add_nonneg (atom0381Coded_nonneg g hg hA hB) (atom0382Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0383Coded_nonneg g hg hA hB) (atom0384Coded_nonneg g hg hA hB)) (add_nonneg (atom0385Coded_nonneg g hg hA hB) (add_nonneg (atom0386Coded_nonneg g hg hA hB) (atom0387Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0388Coded_nonneg g hg hA hB) (atom0389Coded_nonneg g hg hA hB)) (add_nonneg (atom0390Coded_nonneg g hg hA hB) (add_nonneg (atom0391Coded_nonneg g hg hA hB) (atom0392Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
