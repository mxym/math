-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0369 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0369 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 0) * (g 7) * (g 20)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145973111961600 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369Coded : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 1))]
theorem atom0369Coded_decode : atom0369 = SparsePolynomial.decodeCubic 24 atom0369Coded := by decide +kernel
theorem atom0369Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) := by
  have h := atom0369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0370 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0370 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 0) * (g 7) * (g 21)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91276900915200 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370Coded : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 1))]
theorem atom0370Coded_decode : atom0370 = SparsePolynomial.decodeCubic 24 atom0370Coded := by decide +kernel
theorem atom0370Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded) := by
  have h := atom0370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0371 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0371 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 0) * (g 7) * (g 22)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101070199171200 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371Coded : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 1))]
theorem atom0371Coded_decode : atom0371 = SparsePolynomial.decodeCubic 24 atom0371Coded := by decide +kernel
theorem atom0371Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) := by
  have h := atom0371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0372 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0372 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 0) * (g 7) * (g 23)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66423577651200 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372Coded : CoefficientMerge.Poly := [(nat_lit 191, Int.ofNat (nat_lit 1))]
theorem atom0372Coded_decode : atom0372 = SparsePolynomial.decodeCubic 24 atom0372Coded := by decide +kernel
theorem atom0372Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) := by
  have h := atom0372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0373 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130635871027200 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373Coded : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 1))]
theorem atom0373Coded_decode : atom0373 = SparsePolynomial.decodeCubic 24 atom0373Coded := by decide +kernel
theorem atom0373Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded) := by
  have h := atom0373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0374 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0374 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238603162254336 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374Coded : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 1))]
theorem atom0374Coded_decode : atom0374 = SparsePolynomial.decodeCubic 24 atom0374Coded := by decide +kernel
theorem atom0374Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) := by
  have h := atom0374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0375 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0375 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205050002305500 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375Coded : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 1))]
theorem atom0375Coded_decode : atom0375 = SparsePolynomial.decodeCubic 24 atom0375Coded := by decide +kernel
theorem atom0375Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded) := by
  have h := atom0375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0376 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0376 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206244770071032 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376Coded : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 1))]
theorem atom0376Coded_decode : atom0376 = SparsePolynomial.decodeCubic 24 atom0376Coded := by decide +kernel
theorem atom0376Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) := by
  have h := atom0376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0377 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0377 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254087646219792 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377Coded : CoefficientMerge.Poly := [(nat_lit 204, Int.ofNat (nat_lit 1))]
theorem atom0377Coded_decode : atom0377 = SparsePolynomial.decodeCubic 24 atom0377Coded := by decide +kernel
theorem atom0377Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) := by
  have h := atom0377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0378 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0378 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238680835192800 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378Coded : CoefficientMerge.Poly := [(nat_lit 205, Int.ofNat (nat_lit 1))]
theorem atom0378Coded_decode : atom0378 = SparsePolynomial.decodeCubic 24 atom0378Coded := by decide +kernel
theorem atom0378Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded) := by
  have h := atom0378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0379 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0379 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216844064236800 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379Coded : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 1))]
theorem atom0379Coded_decode : atom0379 = SparsePolynomial.decodeCubic 24 atom0379Coded := by decide +kernel
theorem atom0379Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) := by
  have h := atom0379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0380 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0380 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 0) * (g 8) * (g 15)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222147409478400 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380Coded : CoefficientMerge.Poly := [(nat_lit 207, Int.ofNat (nat_lit 1))]
theorem atom0380Coded_decode : atom0380 = SparsePolynomial.decodeCubic 24 atom0380Coded := by decide +kernel
theorem atom0380Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded) := by
  have h := atom0380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0381 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 0) * (g 8) * (g 16)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230406382281600 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381Coded : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 1))]
theorem atom0381Coded_decode : atom0381 = SparsePolynomial.decodeCubic 24 atom0381Coded := by decide +kernel
theorem atom0381Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) := by
  have h := atom0381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0382 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0382 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 0) * (g 8) * (g 17)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236182170470400 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382Coded : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 1))]
theorem atom0382Coded_decode : atom0382 = SparsePolynomial.decodeCubic 24 atom0382Coded := by decide +kernel
theorem atom0382Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) := by
  have h := atom0382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0383 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0383 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 0) * (g 8) * (g 18)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254053174636800 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383Coded : CoefficientMerge.Poly := [(nat_lit 210, Int.ofNat (nat_lit 1))]
theorem atom0383Coded_decode : atom0383 = SparsePolynomial.decodeCubic 24 atom0383Coded := by decide +kernel
theorem atom0383Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded) := by
  have h := atom0383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0384 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0384 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 0) * (g 8) * (g 19)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193981723689600 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384Coded : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 1))]
theorem atom0384Coded_decode : atom0384 = SparsePolynomial.decodeCubic 24 atom0384Coded := by decide +kernel
theorem atom0384Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) := by
  have h := atom0384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0385 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0385 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 0) * (g 8) * (g 20)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155076940972800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385Coded : CoefficientMerge.Poly := [(nat_lit 212, Int.ofNat (nat_lit 1))]
theorem atom0385Coded_decode : atom0385 = SparsePolynomial.decodeCubic 24 atom0385Coded := by decide +kernel
theorem atom0385Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded) := by
  have h := atom0385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0386 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0386 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 0) * (g 8) * (g 21)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102043327478400 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386Coded : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 1))]
theorem atom0386Coded_decode : atom0386 = SparsePolynomial.decodeCubic 24 atom0386Coded := by decide +kernel
theorem atom0386Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) := by
  have h := atom0386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0387 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0387 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 0) * (g 8) * (g 22)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111957702998400 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387Coded : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 1))]
theorem atom0387Coded_decode : atom0387 = SparsePolynomial.decodeCubic 24 atom0387Coded := by decide +kernel
theorem atom0387Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) := by
  have h := atom0387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0388 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0388 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 0) * (g 8) * (g 23)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77432158742400 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388Coded : CoefficientMerge.Poly := [(nat_lit 215, Int.ofNat (nat_lit 1))]
theorem atom0388Coded_decode : atom0388 = SparsePolynomial.decodeCubic 24 atom0388Coded := by decide +kernel
theorem atom0388Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded) := by
  have h := atom0388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0389 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144531443713536 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389Coded : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 1))]
theorem atom0389Coded_decode : atom0389 = SparsePolynomial.decodeCubic 24 atom0389Coded := by decide +kernel
theorem atom0389Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) := by
  have h := atom0389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0390 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0390 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253532085092352 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390Coded : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 1))]
theorem atom0390Coded_decode : atom0390 = SparsePolynomial.decodeCubic 24 atom0390Coded := by decide +kernel
theorem atom0390Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded) := by
  have h := atom0390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0391 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0391 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229630294124352 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391Coded : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 1))]
theorem atom0391Coded_decode : atom0391 = SparsePolynomial.decodeCubic 24 atom0391Coded := by decide +kernel
theorem atom0391Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) := by
  have h := atom0391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0392 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0392 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266810264348760 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392Coded : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 1))]
theorem atom0392Coded_decode : atom0392 = SparsePolynomial.decodeCubic 24 atom0392Coded := by decide +kernel
theorem atom0392Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) := by
  have h := atom0392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0393 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250127712393768 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393Coded : CoefficientMerge.Poly := [(nat_lit 229, Int.ofNat (nat_lit 1))]
theorem atom0393Coded_decode : atom0393 = SparsePolynomial.decodeCubic 24 atom0393Coded := by decide +kernel
theorem atom0393Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded) := by
  have h := atom0393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0394 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0394 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (227785960653768 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394Coded : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 1))]
theorem atom0394Coded_decode : atom0394 = SparsePolynomial.decodeCubic 24 atom0394Coded := by decide +kernel
theorem atom0394Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) := by
  have h := atom0394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0395 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0395 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 0) * (g 9) * (g 15)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232584325111368 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395Coded : CoefficientMerge.Poly := [(nat_lit 231, Int.ofNat (nat_lit 1))]
theorem atom0395Coded_decode : atom0395 = SparsePolynomial.decodeCubic 24 atom0395Coded := by decide +kernel
theorem atom0395Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded) := by
  have h := atom0395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0396 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0396 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 0) * (g 9) * (g 16)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (240338317130568 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396Coded : CoefficientMerge.Poly := [(nat_lit 232, Int.ofNat (nat_lit 1))]
theorem atom0396Coded_decode : atom0396 = SparsePolynomial.decodeCubic 24 atom0396Coded := by decide +kernel
theorem atom0396Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) := by
  have h := atom0396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0397 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0397 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 0) * (g 9) * (g 17)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245609124535368 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397Coded : CoefficientMerge.Poly := [(nat_lit 233, Int.ofNat (nat_lit 1))]
theorem atom0397Coded_decode : atom0397 = SparsePolynomial.decodeCubic 24 atom0397Coded := by decide +kernel
theorem atom0397Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) := by
  have h := atom0397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0398 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0398 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 0) * (g 9) * (g 18)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264258199992996 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398Coded : CoefficientMerge.Poly := [(nat_lit 234, Int.ofNat (nat_lit 1))]
theorem atom0398Coded_decode : atom0398 = SparsePolynomial.decodeCubic 24 atom0398Coded := by decide +kernel
theorem atom0398Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded) := by
  have h := atom0398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0399 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0399 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 0) * (g 9) * (g 19)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206247872412252 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399Coded : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 1))]
theorem atom0399Coded_decode : atom0399 = SparsePolynomial.decodeCubic 24 atom0399Coded := by decide +kernel
theorem atom0399Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) := by
  have h := atom0399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0400 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0400 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 0) * (g 9) * (g 20)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170868583296972 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400Coded : CoefficientMerge.Poly := [(nat_lit 236, Int.ofNat (nat_lit 1))]
theorem atom0400Coded_decode : atom0400 = SparsePolynomial.decodeCubic 24 atom0400Coded := by decide +kernel
theorem atom0400Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded) := by
  have h := atom0400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0401 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0401 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 0) * (g 9) * (g 21)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120997827084420 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401Coded : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 1))]
theorem atom0401Coded_decode : atom0401 = SparsePolynomial.decodeCubic 24 atom0401Coded := by decide +kernel
theorem atom0401Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) := by
  have h := atom0401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0402 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0402 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 0) * (g 9) * (g 22)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126521758552140 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402Coded : CoefficientMerge.Poly := [(nat_lit 238, Int.ofNat (nat_lit 1))]
theorem atom0402Coded_decode : atom0402 = SparsePolynomial.decodeCubic 24 atom0402Coded := by decide +kernel
theorem atom0402Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) := by
  have h := atom0402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0403 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0403 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 0) * (g 9) * (g 23)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96623441813052 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403Coded : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 1))]
theorem atom0403Coded_decode : atom0403 = SparsePolynomial.decodeCubic 24 atom0403Coded := by decide +kernel
theorem atom0403Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded) := by
  have h := atom0403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0404 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145564793865216 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404Coded : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 1))]
theorem atom0404Coded_decode : atom0404 = SparsePolynomial.decodeCubic 24 atom0404Coded := by decide +kernel
theorem atom0404Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) := by
  have h := atom0404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0405 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0405 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266333360622912 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405Coded : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 1))]
theorem atom0405Coded_decode : atom0405 = SparsePolynomial.decodeCubic 24 atom0405Coded := by decide +kernel
theorem atom0405Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded) := by
  have h := atom0405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0406 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0406 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (281629959463512 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406Coded : CoefficientMerge.Poly := [(nat_lit 252, Int.ofNat (nat_lit 1))]
theorem atom0406Coded_decode : atom0406 = SparsePolynomial.decodeCubic 24 atom0406Coded := by decide +kernel
theorem atom0406Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) := by
  have h := atom0406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0407 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0407 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262721401588008 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407Coded : CoefficientMerge.Poly := [(nat_lit 253, Int.ofNat (nat_lit 1))]
theorem atom0407Coded_decode : atom0407 = SparsePolynomial.decodeCubic 24 atom0407Coded := by decide +kernel
theorem atom0407Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) := by
  have h := atom0407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0408 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0408 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (239619520878408 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408Coded : CoefficientMerge.Poly := [(nat_lit 254, Int.ofNat (nat_lit 1))]
theorem atom0408Coded_decode : atom0408 = SparsePolynomial.decodeCubic 24 atom0408Coded := by decide +kernel
theorem atom0408Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded) := by
  have h := atom0408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0409 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 0) * (g 10) * (g 15)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (243657756366408 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409Coded : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 1))]
theorem atom0409Coded_decode : atom0409 = SparsePolynomial.decodeCubic 24 atom0409Coded := by decide +kernel
theorem atom0409Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) := by
  have h := atom0409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0410 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 0) * (g 10) * (g 16)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250651619416008 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410Coded : CoefficientMerge.Poly := [(nat_lit 256, Int.ofNat (nat_lit 1))]
theorem atom0410Coded_decode : atom0410 = SparsePolynomial.decodeCubic 24 atom0410Coded := by decide +kernel
theorem atom0410Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded) := by
  have h := atom0410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0411 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 0) * (g 10) * (g 17)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (255162297851208 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411Coded : CoefficientMerge.Poly := [(nat_lit 257, Int.ofNat (nat_lit 1))]
theorem atom0411Coded_decode : atom0411 = SparsePolynomial.decodeCubic 24 atom0411Coded := by decide +kernel
theorem atom0411Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) := by
  have h := atom0411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0412 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 0) * (g 10) * (g 18)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276374549456676 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412Coded : CoefficientMerge.Poly := [(nat_lit 258, Int.ofNat (nat_lit 1))]
theorem atom0412Coded_decode : atom0412 = SparsePolynomial.decodeCubic 24 atom0412Coded := by decide +kernel
theorem atom0412Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) := by
  have h := atom0412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0413 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 0) * (g 10) * (g 19)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224250703141212 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413Coded : CoefficientMerge.Poly := [(nat_lit 259, Int.ofNat (nat_lit 1))]
theorem atom0413Coded_decode : atom0413 = SparsePolynomial.decodeCubic 24 atom0413Coded := by decide +kernel
theorem atom0413Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded) := by
  have h := atom0413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0414 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 0) * (g 10) * (g 20)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202038123520332 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414Coded : CoefficientMerge.Poly := [(nat_lit 260, Int.ofNat (nat_lit 1))]
theorem atom0414Coded_decode : atom0414 = SparsePolynomial.decodeCubic 24 atom0414Coded := by decide +kernel
theorem atom0414Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) := by
  have h := atom0414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0415 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0415 = ((g 0) * (g 10) * (g 21)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157420230578820 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415Coded : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 1))]
theorem atom0415Coded_decode : atom0415 = SparsePolynomial.decodeCubic 24 atom0415Coded := by decide +kernel
theorem atom0415Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded) := by
  have h := atom0415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0416 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0416 = ((g 0) * (g 10) * (g 22)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149012007995340 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416Coded : CoefficientMerge.Poly := [(nat_lit 262, Int.ofNat (nat_lit 1))]
theorem atom0416Coded_decode : atom0416 = SparsePolynomial.decodeCubic 24 atom0416Coded := by decide +kernel
theorem atom0416Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) := by
  have h := atom0416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0417 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0417 = ((g 0) * (g 10) * (g 23)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131646782756412 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417Coded : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 1))]
theorem atom0417Coded_decode : atom0417 = SparsePolynomial.decodeCubic 24 atom0417Coded := by decide +kernel
theorem atom0417Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) := by
  have h := atom0417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0418 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0418 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159353351125056 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418Coded : CoefficientMerge.Poly := [(nat_lit 275, Int.ofNat (nat_lit 1))]
theorem atom0418Coded_decode : atom0418 = SparsePolynomial.decodeCubic 24 atom0418Coded := by decide +kernel
theorem atom0418Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded) := by
  have h := atom0418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0419 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0419 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (325628128343232 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419Coded : CoefficientMerge.Poly := [(nat_lit 276, Int.ofNat (nat_lit 1))]
theorem atom0419Coded_decode : atom0419 = SparsePolynomial.decodeCubic 24 atom0419Coded := by decide +kernel
theorem atom0419Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) := by
  have h := atom0419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0420 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0420 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (285505542588816 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420Coded : CoefficientMerge.Poly := [(nat_lit 277, Int.ofNat (nat_lit 1))]
theorem atom0420Coded_decode : atom0420 = SparsePolynomial.decodeCubic 24 atom0420Coded := by decide +kernel
theorem atom0420Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded) := by
  have h := atom0420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0421 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0421 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253912851994032 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421Coded : CoefficientMerge.Poly := [(nat_lit 278, Int.ofNat (nat_lit 1))]
theorem atom0421Coded_decode : atom0421 = SparsePolynomial.decodeCubic 24 atom0421Coded := by decide +kernel
theorem atom0421Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) := by
  have h := atom0421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0422 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0422 = ((g 0) * (g 11) * (g 15)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256165050182832 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422Coded : CoefficientMerge.Poly := [(nat_lit 279, Int.ofNat (nat_lit 1))]
theorem atom0422Coded_decode : atom0422 = SparsePolynomial.decodeCubic 24 atom0422Coded := by decide +kernel
theorem atom0422Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) := by
  have h := atom0422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0423 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0423 = ((g 0) * (g 11) * (g 16)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262143636077232 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423Coded : CoefficientMerge.Poly := [(nat_lit 280, Int.ofNat (nat_lit 1))]
theorem atom0423Coded_decode : atom0423 = SparsePolynomial.decodeCubic 24 atom0423Coded := by decide +kernel
theorem atom0423Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded) := by
  have h := atom0423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0424 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0424 = ((g 0) * (g 11) * (g 17)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265639037357232 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424Coded : CoefficientMerge.Poly := [(nat_lit 281, Int.ofNat (nat_lit 1))]
theorem atom0424Coded_decode : atom0424 = SparsePolynomial.decodeCubic 24 atom0424Coded := by decide +kernel
theorem atom0424Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) := by
  have h := atom0424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0425 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0425 = ((g 0) * (g 11) * (g 18)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291518936774208 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425Coded : CoefficientMerge.Poly := [(nat_lit 282, Int.ofNat (nat_lit 1))]
theorem atom0425Coded_decode : atom0425 = SparsePolynomial.decodeCubic 24 atom0425Coded := by decide +kernel
theorem atom0425Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded) := by
  have h := atom0425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0426 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0426 = ((g 0) * (g 11) * (g 19)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241024102148016 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426Coded : CoefficientMerge.Poly := [(nat_lit 283, Int.ofNat (nat_lit 1))]
theorem atom0426Coded_decode : atom0426 = SparsePolynomial.decodeCubic 24 atom0426Coded := by decide +kernel
theorem atom0426Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) := by
  have h := atom0426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0427 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0427 = ((g 0) * (g 11) * (g 20)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231218915577408 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427Coded : CoefficientMerge.Poly := [(nat_lit 284, Int.ofNat (nat_lit 1))]
theorem atom0427Coded_decode : atom0427 = SparsePolynomial.decodeCubic 24 atom0427Coded := by decide +kernel
theorem atom0427Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) := by
  have h := atom0427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0428 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0428 = ((g 0) * (g 11) * (g 21)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188817502897584 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428Coded : CoefficientMerge.Poly := [(nat_lit 285, Int.ofNat (nat_lit 1))]
theorem atom0428Coded_decode : atom0428 = SparsePolynomial.decodeCubic 24 atom0428Coded := by decide +kernel
theorem atom0428Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded) := by
  have h := atom0428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0429 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0429 = ((g 0) * (g 11) * (g 22)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166489350215040 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429Coded : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 1))]
theorem atom0429Coded_decode : atom0429 = SparsePolynomial.decodeCubic 24 atom0429Coded := by decide +kernel
theorem atom0429Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) := by
  have h := atom0429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0430 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0430 = ((g 0) * (g 11) * (g 23)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159211799569152 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430Coded : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 1))]
theorem atom0430Coded_decode : atom0430 = SparsePolynomial.decodeCubic 24 atom0430Coded := by decide +kernel
theorem atom0430Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded) := by
  have h := atom0430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0431 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0431 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204859561585536 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431Coded : CoefficientMerge.Poly := [(nat_lit 300, Int.ofNat (nat_lit 1))]
theorem atom0431Coded_decode : atom0431 = SparsePolynomial.decodeCubic 24 atom0431Coded := by decide +kernel
theorem atom0431Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) := by
  have h := atom0431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0432 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0432 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (363727996258176 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432Coded : CoefficientMerge.Poly := [(nat_lit 301, Int.ofNat (nat_lit 1))]
theorem atom0432Coded_decode : atom0432 = SparsePolynomial.decodeCubic 24 atom0432Coded := by decide +kernel
theorem atom0432Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) := by
  have h := atom0432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0433 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0433 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (314919946272096 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433Coded : CoefficientMerge.Poly := [(nat_lit 302, Int.ofNat (nat_lit 1))]
theorem atom0433Coded_decode : atom0433 = SparsePolynomial.decodeCubic 24 atom0433Coded := by decide +kernel
theorem atom0433Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded) := by
  have h := atom0433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0434 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0434 = ((g 0) * (g 12) * (g 15)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (314422158328992 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434Coded : CoefficientMerge.Poly := [(nat_lit 303, Int.ofNat (nat_lit 1))]
theorem atom0434Coded_decode : atom0434 = SparsePolynomial.decodeCubic 24 atom0434Coded := by decide +kernel
theorem atom0434Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) := by
  have h := atom0434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0435 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0435 = ((g 0) * (g 12) * (g 16)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (319130318882592 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435Coded : CoefficientMerge.Poly := [(nat_lit 304, Int.ofNat (nat_lit 1))]
theorem atom0435Coded_decode : atom0435 = SparsePolynomial.decodeCubic 24 atom0435Coded := by decide +kernel
theorem atom0435Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded) := by
  have h := atom0435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0436 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0436 = ((g 0) * (g 12) * (g 17)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321355294821792 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436Coded : CoefficientMerge.Poly := [(nat_lit 305, Int.ofNat (nat_lit 1))]
theorem atom0436Coded_decode : atom0436 = SparsePolynomial.decodeCubic 24 atom0436Coded := by decide +kernel
theorem atom0436Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) := by
  have h := atom0436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0437 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0437 = ((g 0) * (g 12) * (g 18)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352380815538048 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437Coded : CoefficientMerge.Poly := [(nat_lit 306, Int.ofNat (nat_lit 1))]
theorem atom0437Coded_decode : atom0437 = SparsePolynomial.decodeCubic 24 atom0437Coded := by decide +kernel
theorem atom0437Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) := by
  have h := atom0437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0438 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0438 = ((g 0) * (g 12) * (g 19)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291890417851296 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438Coded : CoefficientMerge.Poly := [(nat_lit 307, Int.ofNat (nat_lit 1))]
theorem atom0438Coded_decode : atom0438 = SparsePolynomial.decodeCubic 24 atom0438Coded := by decide +kernel
theorem atom0438Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded) := by
  have h := atom0438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0439 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0439 = ((g 0) * (g 12) * (g 20)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (294121979826048 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439Coded : CoefficientMerge.Poly := [(nat_lit 308, Int.ofNat (nat_lit 1))]
theorem atom0439Coded_decode : atom0439 = SparsePolynomial.decodeCubic 24 atom0439Coded := by decide +kernel
theorem atom0439Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) := by
  have h := atom0439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0440 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0440 = ((g 0) * (g 12) * (g 21)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232524785759904 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440Coded : CoefficientMerge.Poly := [(nat_lit 309, Int.ofNat (nat_lit 1))]
theorem atom0440Coded_decode : atom0440 = SparsePolynomial.decodeCubic 24 atom0440Coded := by decide +kernel
theorem atom0440Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded) := by
  have h := atom0440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0441 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0441 = ((g 0) * (g 12) * (g 22)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163964446295040 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441Coded : CoefficientMerge.Poly := [(nat_lit 310, Int.ofNat (nat_lit 1))]
theorem atom0441Coded_decode : atom0441 = SparsePolynomial.decodeCubic 24 atom0441Coded := by decide +kernel
theorem atom0441Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) := by
  have h := atom0441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0442 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0442 = ((g 0) * (g 12) * (g 23)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152337682202112 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442Coded : CoefficientMerge.Poly := [(nat_lit 311, Int.ofNat (nat_lit 1))]
theorem atom0442Coded_decode : atom0442 = SparsePolynomial.decodeCubic 24 atom0442Coded := by decide +kernel
theorem atom0442Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) := by
  have h := atom0442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0443 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0443 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197453219040000 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443Coded : CoefficientMerge.Poly := [(nat_lit 325, Int.ofNat (nat_lit 1))]
theorem atom0443Coded_decode : atom0443 = SparsePolynomial.decodeCubic 24 atom0443Coded := by decide +kernel
theorem atom0443Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded) := by
  have h := atom0443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0444 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0444 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (339075700064640 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444Coded : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 1))]
theorem atom0444Coded_decode : atom0444 = SparsePolynomial.decodeCubic 24 atom0444Coded := by decide +kernel
theorem atom0444Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) := by
  have h := atom0444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0445 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0445 = ((g 0) * (g 13) * (g 15)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (310411363872960 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445Coded : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 1))]
theorem atom0445Coded_decode : atom0445 = SparsePolynomial.decodeCubic 24 atom0445Coded := by decide +kernel
theorem atom0445Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded) := by
  have h := atom0445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0446 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0446 = ((g 0) * (g 13) * (g 16)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (310881610468800 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446Coded : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 1))]
theorem atom0446Coded_decode : atom0446 = SparsePolynomial.decodeCubic 24 atom0446Coded := by decide +kernel
theorem atom0446Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) := by
  have h := atom0446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0447 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0447 = ((g 0) * (g 13) * (g 17)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311581012881600 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447Coded : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 1))]
theorem atom0447Coded_decode : atom0447 = SparsePolynomial.decodeCubic 24 atom0447Coded := by decide +kernel
theorem atom0447Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) := by
  have h := atom0447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0448 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0448 = ((g 0) * (g 13) * (g 18)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340076468793600 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448Coded : CoefficientMerge.Poly := [(nat_lit 330, Int.ofNat (nat_lit 1))]
theorem atom0448Coded_decode : atom0448 = SparsePolynomial.decodeCubic 24 atom0448Coded := by decide +kernel
theorem atom0448Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded) := by
  have h := atom0448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800)), (nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400)), (nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996)), (nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408)), (nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056)), (nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584)), (nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296)), (nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
def block007_data_flat000 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600))]
theorem block007_data_flat000_step : block007_data_flat000 = (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) := by decide +kernel
theorem block007_data_flat000_original : block007_data_flat000 = (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) := by
  rw [block007_data_flat000_step]
def block007_data_flat001 : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 91276900915200))]
theorem block007_data_flat001_step : block007_data_flat001 = (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded) := by decide +kernel
theorem block007_data_flat001_original : block007_data_flat001 = (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded) := by
  rw [block007_data_flat001_step]
def block007_data_flat002 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200))]
theorem block007_data_flat002_step : block007_data_flat002 = (CoefficientMerge.fastMerge block007_data_flat000 block007_data_flat001) := by decide +kernel
theorem block007_data_flat002_original : block007_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) := by
  rw [block007_data_flat002_step, block007_data_flat000_original, block007_data_flat001_original]
def block007_data_flat003 : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 101070199171200))]
theorem block007_data_flat003_step : block007_data_flat003 = (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) := by decide +kernel
theorem block007_data_flat003_original : block007_data_flat003 = (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) := by
  rw [block007_data_flat003_step]
def block007_data_flat004 : CoefficientMerge.Poly := [(nat_lit 191, Int.ofNat (nat_lit 66423577651200))]
theorem block007_data_flat004_step : block007_data_flat004 = (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) := by decide +kernel
theorem block007_data_flat004_original : block007_data_flat004 = (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) := by
  rw [block007_data_flat004_step]
def block007_data_flat005 : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 130635871027200))]
theorem block007_data_flat005_step : block007_data_flat005 = (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded) := by decide +kernel
theorem block007_data_flat005_original : block007_data_flat005 = (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded) := by
  rw [block007_data_flat005_step]
def block007_data_flat006 : CoefficientMerge.Poly := [(nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200))]
theorem block007_data_flat006_step : block007_data_flat006 = (CoefficientMerge.fastMerge block007_data_flat004 block007_data_flat005) := by decide +kernel
theorem block007_data_flat006_original : block007_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)) := by
  rw [block007_data_flat006_step, block007_data_flat004_original, block007_data_flat005_original]
def block007_data_flat007 : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200))]
theorem block007_data_flat007_step : block007_data_flat007 = (CoefficientMerge.fastMerge block007_data_flat003 block007_data_flat006) := by decide +kernel
theorem block007_data_flat007_original : block007_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded))) := by
  rw [block007_data_flat007_step, block007_data_flat003_original, block007_data_flat006_original]
def block007_data_flat008 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200))]
theorem block007_data_flat008_step : block007_data_flat008 = (CoefficientMerge.fastMerge block007_data_flat002 block007_data_flat007) := by decide +kernel
theorem block007_data_flat008_original : block007_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) := by
  rw [block007_data_flat008_step, block007_data_flat002_original, block007_data_flat007_original]
def block007_data_flat009 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 238603162254336))]
theorem block007_data_flat009_step : block007_data_flat009 = (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) := by decide +kernel
theorem block007_data_flat009_original : block007_data_flat009 = (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) := by
  rw [block007_data_flat009_step]
def block007_data_flat010 : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 205050002305500))]
theorem block007_data_flat010_step : block007_data_flat010 = (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded) := by decide +kernel
theorem block007_data_flat010_original : block007_data_flat010 = (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded) := by
  rw [block007_data_flat010_step]
def block007_data_flat011 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500))]
theorem block007_data_flat011_step : block007_data_flat011 = (CoefficientMerge.fastMerge block007_data_flat009 block007_data_flat010) := by decide +kernel
theorem block007_data_flat011_original : block007_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) := by
  rw [block007_data_flat011_step, block007_data_flat009_original, block007_data_flat010_original]
def block007_data_flat012 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 206244770071032))]
theorem block007_data_flat012_step : block007_data_flat012 = (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) := by decide +kernel
theorem block007_data_flat012_original : block007_data_flat012 = (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) := by
  rw [block007_data_flat012_step]
def block007_data_flat013 : CoefficientMerge.Poly := [(nat_lit 204, Int.ofNat (nat_lit 254087646219792))]
theorem block007_data_flat013_step : block007_data_flat013 = (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) := by decide +kernel
theorem block007_data_flat013_original : block007_data_flat013 = (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) := by
  rw [block007_data_flat013_step]
def block007_data_flat014 : CoefficientMerge.Poly := [(nat_lit 205, Int.ofNat (nat_lit 238680835192800))]
theorem block007_data_flat014_step : block007_data_flat014 = (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded) := by decide +kernel
theorem block007_data_flat014_original : block007_data_flat014 = (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded) := by
  rw [block007_data_flat014_step]
def block007_data_flat015 : CoefficientMerge.Poly := [(nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800))]
theorem block007_data_flat015_step : block007_data_flat015 = (CoefficientMerge.fastMerge block007_data_flat013 block007_data_flat014) := by decide +kernel
theorem block007_data_flat015_original : block007_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded)) := by
  rw [block007_data_flat015_step, block007_data_flat013_original, block007_data_flat014_original]
def block007_data_flat016 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800))]
theorem block007_data_flat016_step : block007_data_flat016 = (CoefficientMerge.fastMerge block007_data_flat012 block007_data_flat015) := by decide +kernel
theorem block007_data_flat016_original : block007_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))) := by
  rw [block007_data_flat016_step, block007_data_flat012_original, block007_data_flat015_original]
def block007_data_flat017 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800))]
theorem block007_data_flat017_step : block007_data_flat017 = (CoefficientMerge.fastMerge block007_data_flat011 block007_data_flat016) := by decide +kernel
theorem block007_data_flat017_original : block007_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded)))) := by
  rw [block007_data_flat017_step, block007_data_flat011_original, block007_data_flat016_original]
def block007_data_flat018 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800))]
theorem block007_data_flat018_step : block007_data_flat018 = (CoefficientMerge.fastMerge block007_data_flat008 block007_data_flat017) := by decide +kernel
theorem block007_data_flat018_original : block007_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) := by
  rw [block007_data_flat018_step, block007_data_flat008_original, block007_data_flat017_original]
def block007_data_flat019 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 216844064236800))]
theorem block007_data_flat019_step : block007_data_flat019 = (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) := by decide +kernel
theorem block007_data_flat019_original : block007_data_flat019 = (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) := by
  rw [block007_data_flat019_step]
def block007_data_flat020 : CoefficientMerge.Poly := [(nat_lit 207, Int.ofNat (nat_lit 222147409478400))]
theorem block007_data_flat020_step : block007_data_flat020 = (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded) := by decide +kernel
theorem block007_data_flat020_original : block007_data_flat020 = (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded) := by
  rw [block007_data_flat020_step]
def block007_data_flat021 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400))]
theorem block007_data_flat021_step : block007_data_flat021 = (CoefficientMerge.fastMerge block007_data_flat019 block007_data_flat020) := by decide +kernel
theorem block007_data_flat021_original : block007_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) := by
  rw [block007_data_flat021_step, block007_data_flat019_original, block007_data_flat020_original]
def block007_data_flat022 : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 230406382281600))]
theorem block007_data_flat022_step : block007_data_flat022 = (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) := by decide +kernel
theorem block007_data_flat022_original : block007_data_flat022 = (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) := by
  rw [block007_data_flat022_step]
def block007_data_flat023 : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 236182170470400))]
theorem block007_data_flat023_step : block007_data_flat023 = (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) := by decide +kernel
theorem block007_data_flat023_original : block007_data_flat023 = (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) := by
  rw [block007_data_flat023_step]
def block007_data_flat024 : CoefficientMerge.Poly := [(nat_lit 210, Int.ofNat (nat_lit 254053174636800))]
theorem block007_data_flat024_step : block007_data_flat024 = (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded) := by decide +kernel
theorem block007_data_flat024_original : block007_data_flat024 = (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded) := by
  rw [block007_data_flat024_step]
def block007_data_flat025 : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800))]
theorem block007_data_flat025_step : block007_data_flat025 = (CoefficientMerge.fastMerge block007_data_flat023 block007_data_flat024) := by decide +kernel
theorem block007_data_flat025_original : block007_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)) := by
  rw [block007_data_flat025_step, block007_data_flat023_original, block007_data_flat024_original]
def block007_data_flat026 : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800))]
theorem block007_data_flat026_step : block007_data_flat026 = (CoefficientMerge.fastMerge block007_data_flat022 block007_data_flat025) := by decide +kernel
theorem block007_data_flat026_original : block007_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded))) := by
  rw [block007_data_flat026_step, block007_data_flat022_original, block007_data_flat025_original]
def block007_data_flat027 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800))]
theorem block007_data_flat027_step : block007_data_flat027 = (CoefficientMerge.fastMerge block007_data_flat021 block007_data_flat026) := by decide +kernel
theorem block007_data_flat027_original : block007_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) := by
  rw [block007_data_flat027_step, block007_data_flat021_original, block007_data_flat026_original]
def block007_data_flat028 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 193981723689600))]
theorem block007_data_flat028_step : block007_data_flat028 = (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) := by decide +kernel
theorem block007_data_flat028_original : block007_data_flat028 = (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) := by
  rw [block007_data_flat028_step]
def block007_data_flat029 : CoefficientMerge.Poly := [(nat_lit 212, Int.ofNat (nat_lit 155076940972800))]
theorem block007_data_flat029_step : block007_data_flat029 = (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded) := by decide +kernel
theorem block007_data_flat029_original : block007_data_flat029 = (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded) := by
  rw [block007_data_flat029_step]
def block007_data_flat030 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800))]
theorem block007_data_flat030_step : block007_data_flat030 = (CoefficientMerge.fastMerge block007_data_flat028 block007_data_flat029) := by decide +kernel
theorem block007_data_flat030_original : block007_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) := by
  rw [block007_data_flat030_step, block007_data_flat028_original, block007_data_flat029_original]
def block007_data_flat031 : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 102043327478400))]
theorem block007_data_flat031_step : block007_data_flat031 = (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) := by decide +kernel
theorem block007_data_flat031_original : block007_data_flat031 = (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) := by
  rw [block007_data_flat031_step]
def block007_data_flat032 : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 111957702998400))]
theorem block007_data_flat032_step : block007_data_flat032 = (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) := by decide +kernel
theorem block007_data_flat032_original : block007_data_flat032 = (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) := by
  rw [block007_data_flat032_step]
def block007_data_flat033 : CoefficientMerge.Poly := [(nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat033_step : block007_data_flat033 = (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded) := by decide +kernel
theorem block007_data_flat033_original : block007_data_flat033 = (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded) := by
  rw [block007_data_flat033_step]
def block007_data_flat034 : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat034_step : block007_data_flat034 = (CoefficientMerge.fastMerge block007_data_flat032 block007_data_flat033) := by decide +kernel
theorem block007_data_flat034_original : block007_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)) := by
  rw [block007_data_flat034_step, block007_data_flat032_original, block007_data_flat033_original]
def block007_data_flat035 : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat035_step : block007_data_flat035 = (CoefficientMerge.fastMerge block007_data_flat031 block007_data_flat034) := by decide +kernel
theorem block007_data_flat035_original : block007_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded))) := by
  rw [block007_data_flat035_step, block007_data_flat031_original, block007_data_flat034_original]
def block007_data_flat036 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat036_step : block007_data_flat036 = (CoefficientMerge.fastMerge block007_data_flat030 block007_data_flat035) := by decide +kernel
theorem block007_data_flat036_original : block007_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))) := by
  rw [block007_data_flat036_step, block007_data_flat030_original, block007_data_flat035_original]
def block007_data_flat037 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat037_step : block007_data_flat037 = (CoefficientMerge.fastMerge block007_data_flat027 block007_data_flat036) := by decide +kernel
theorem block007_data_flat037_original : block007_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded))))) := by
  rw [block007_data_flat037_step, block007_data_flat027_original, block007_data_flat036_original]
def block007_data_flat038 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800)), (nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400))]
theorem block007_data_flat038_step : block007_data_flat038 = (CoefficientMerge.fastMerge block007_data_flat018 block007_data_flat037) := by decide +kernel
theorem block007_data_flat038_original : block007_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) := by
  rw [block007_data_flat038_step, block007_data_flat018_original, block007_data_flat037_original]
def block007_data_flat039 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 144531443713536))]
theorem block007_data_flat039_step : block007_data_flat039 = (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) := by decide +kernel
theorem block007_data_flat039_original : block007_data_flat039 = (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) := by
  rw [block007_data_flat039_step]
def block007_data_flat040 : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 253532085092352))]
theorem block007_data_flat040_step : block007_data_flat040 = (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded) := by decide +kernel
theorem block007_data_flat040_original : block007_data_flat040 = (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded) := by
  rw [block007_data_flat040_step]
def block007_data_flat041 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352))]
theorem block007_data_flat041_step : block007_data_flat041 = (CoefficientMerge.fastMerge block007_data_flat039 block007_data_flat040) := by decide +kernel
theorem block007_data_flat041_original : block007_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) := by
  rw [block007_data_flat041_step, block007_data_flat039_original, block007_data_flat040_original]
def block007_data_flat042 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 229630294124352))]
theorem block007_data_flat042_step : block007_data_flat042 = (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) := by decide +kernel
theorem block007_data_flat042_original : block007_data_flat042 = (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) := by
  rw [block007_data_flat042_step]
def block007_data_flat043 : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 266810264348760))]
theorem block007_data_flat043_step : block007_data_flat043 = (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) := by decide +kernel
theorem block007_data_flat043_original : block007_data_flat043 = (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) := by
  rw [block007_data_flat043_step]
def block007_data_flat044 : CoefficientMerge.Poly := [(nat_lit 229, Int.ofNat (nat_lit 250127712393768))]
theorem block007_data_flat044_step : block007_data_flat044 = (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded) := by decide +kernel
theorem block007_data_flat044_original : block007_data_flat044 = (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded) := by
  rw [block007_data_flat044_step]
def block007_data_flat045 : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768))]
theorem block007_data_flat045_step : block007_data_flat045 = (CoefficientMerge.fastMerge block007_data_flat043 block007_data_flat044) := by decide +kernel
theorem block007_data_flat045_original : block007_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)) := by
  rw [block007_data_flat045_step, block007_data_flat043_original, block007_data_flat044_original]
def block007_data_flat046 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768))]
theorem block007_data_flat046_step : block007_data_flat046 = (CoefficientMerge.fastMerge block007_data_flat042 block007_data_flat045) := by decide +kernel
theorem block007_data_flat046_original : block007_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded))) := by
  rw [block007_data_flat046_step, block007_data_flat042_original, block007_data_flat045_original]
def block007_data_flat047 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768))]
theorem block007_data_flat047_step : block007_data_flat047 = (CoefficientMerge.fastMerge block007_data_flat041 block007_data_flat046) := by decide +kernel
theorem block007_data_flat047_original : block007_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) := by
  rw [block007_data_flat047_step, block007_data_flat041_original, block007_data_flat046_original]
def block007_data_flat048 : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 227785960653768))]
theorem block007_data_flat048_step : block007_data_flat048 = (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) := by decide +kernel
theorem block007_data_flat048_original : block007_data_flat048 = (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) := by
  rw [block007_data_flat048_step]
def block007_data_flat049 : CoefficientMerge.Poly := [(nat_lit 231, Int.ofNat (nat_lit 232584325111368))]
theorem block007_data_flat049_step : block007_data_flat049 = (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded) := by decide +kernel
theorem block007_data_flat049_original : block007_data_flat049 = (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded) := by
  rw [block007_data_flat049_step]
def block007_data_flat050 : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368))]
theorem block007_data_flat050_step : block007_data_flat050 = (CoefficientMerge.fastMerge block007_data_flat048 block007_data_flat049) := by decide +kernel
theorem block007_data_flat050_original : block007_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) := by
  rw [block007_data_flat050_step, block007_data_flat048_original, block007_data_flat049_original]
def block007_data_flat051 : CoefficientMerge.Poly := [(nat_lit 232, Int.ofNat (nat_lit 240338317130568))]
theorem block007_data_flat051_step : block007_data_flat051 = (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) := by decide +kernel
theorem block007_data_flat051_original : block007_data_flat051 = (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) := by
  rw [block007_data_flat051_step]
def block007_data_flat052 : CoefficientMerge.Poly := [(nat_lit 233, Int.ofNat (nat_lit 245609124535368))]
theorem block007_data_flat052_step : block007_data_flat052 = (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) := by decide +kernel
theorem block007_data_flat052_original : block007_data_flat052 = (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) := by
  rw [block007_data_flat052_step]
def block007_data_flat053 : CoefficientMerge.Poly := [(nat_lit 234, Int.ofNat (nat_lit 264258199992996))]
theorem block007_data_flat053_step : block007_data_flat053 = (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded) := by decide +kernel
theorem block007_data_flat053_original : block007_data_flat053 = (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded) := by
  rw [block007_data_flat053_step]
def block007_data_flat054 : CoefficientMerge.Poly := [(nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996))]
theorem block007_data_flat054_step : block007_data_flat054 = (CoefficientMerge.fastMerge block007_data_flat052 block007_data_flat053) := by decide +kernel
theorem block007_data_flat054_original : block007_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded)) := by
  rw [block007_data_flat054_step, block007_data_flat052_original, block007_data_flat053_original]
def block007_data_flat055 : CoefficientMerge.Poly := [(nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996))]
theorem block007_data_flat055_step : block007_data_flat055 = (CoefficientMerge.fastMerge block007_data_flat051 block007_data_flat054) := by decide +kernel
theorem block007_data_flat055_original : block007_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))) := by
  rw [block007_data_flat055_step, block007_data_flat051_original, block007_data_flat054_original]
def block007_data_flat056 : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996))]
theorem block007_data_flat056_step : block007_data_flat056 = (CoefficientMerge.fastMerge block007_data_flat050 block007_data_flat055) := by decide +kernel
theorem block007_data_flat056_original : block007_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded)))) := by
  rw [block007_data_flat056_step, block007_data_flat050_original, block007_data_flat055_original]
def block007_data_flat057 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996))]
theorem block007_data_flat057_step : block007_data_flat057 = (CoefficientMerge.fastMerge block007_data_flat047 block007_data_flat056) := by decide +kernel
theorem block007_data_flat057_original : block007_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) := by
  rw [block007_data_flat057_step, block007_data_flat047_original, block007_data_flat056_original]
def block007_data_flat058 : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 206247872412252))]
theorem block007_data_flat058_step : block007_data_flat058 = (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) := by decide +kernel
theorem block007_data_flat058_original : block007_data_flat058 = (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) := by
  rw [block007_data_flat058_step]
def block007_data_flat059 : CoefficientMerge.Poly := [(nat_lit 236, Int.ofNat (nat_lit 170868583296972))]
theorem block007_data_flat059_step : block007_data_flat059 = (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded) := by decide +kernel
theorem block007_data_flat059_original : block007_data_flat059 = (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded) := by
  rw [block007_data_flat059_step]
def block007_data_flat060 : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972))]
theorem block007_data_flat060_step : block007_data_flat060 = (CoefficientMerge.fastMerge block007_data_flat058 block007_data_flat059) := by decide +kernel
theorem block007_data_flat060_original : block007_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) := by
  rw [block007_data_flat060_step, block007_data_flat058_original, block007_data_flat059_original]
def block007_data_flat061 : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 120997827084420))]
theorem block007_data_flat061_step : block007_data_flat061 = (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) := by decide +kernel
theorem block007_data_flat061_original : block007_data_flat061 = (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) := by
  rw [block007_data_flat061_step]
def block007_data_flat062 : CoefficientMerge.Poly := [(nat_lit 238, Int.ofNat (nat_lit 126521758552140))]
theorem block007_data_flat062_step : block007_data_flat062 = (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) := by decide +kernel
theorem block007_data_flat062_original : block007_data_flat062 = (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) := by
  rw [block007_data_flat062_step]
def block007_data_flat063 : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 96623441813052))]
theorem block007_data_flat063_step : block007_data_flat063 = (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded) := by decide +kernel
theorem block007_data_flat063_original : block007_data_flat063 = (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded) := by
  rw [block007_data_flat063_step]
def block007_data_flat064 : CoefficientMerge.Poly := [(nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052))]
theorem block007_data_flat064_step : block007_data_flat064 = (CoefficientMerge.fastMerge block007_data_flat062 block007_data_flat063) := by decide +kernel
theorem block007_data_flat064_original : block007_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)) := by
  rw [block007_data_flat064_step, block007_data_flat062_original, block007_data_flat063_original]
def block007_data_flat065 : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052))]
theorem block007_data_flat065_step : block007_data_flat065 = (CoefficientMerge.fastMerge block007_data_flat061 block007_data_flat064) := by decide +kernel
theorem block007_data_flat065_original : block007_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded))) := by
  rw [block007_data_flat065_step, block007_data_flat061_original, block007_data_flat064_original]
def block007_data_flat066 : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052))]
theorem block007_data_flat066_step : block007_data_flat066 = (CoefficientMerge.fastMerge block007_data_flat060 block007_data_flat065) := by decide +kernel
theorem block007_data_flat066_original : block007_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) := by
  rw [block007_data_flat066_step, block007_data_flat060_original, block007_data_flat065_original]
def block007_data_flat067 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 145564793865216))]
theorem block007_data_flat067_step : block007_data_flat067 = (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) := by decide +kernel
theorem block007_data_flat067_original : block007_data_flat067 = (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) := by
  rw [block007_data_flat067_step]
def block007_data_flat068 : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 266333360622912))]
theorem block007_data_flat068_step : block007_data_flat068 = (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded) := by decide +kernel
theorem block007_data_flat068_original : block007_data_flat068 = (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded) := by
  rw [block007_data_flat068_step]
def block007_data_flat069 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912))]
theorem block007_data_flat069_step : block007_data_flat069 = (CoefficientMerge.fastMerge block007_data_flat067 block007_data_flat068) := by decide +kernel
theorem block007_data_flat069_original : block007_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) := by
  rw [block007_data_flat069_step, block007_data_flat067_original, block007_data_flat068_original]
def block007_data_flat070 : CoefficientMerge.Poly := [(nat_lit 252, Int.ofNat (nat_lit 281629959463512))]
theorem block007_data_flat070_step : block007_data_flat070 = (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) := by decide +kernel
theorem block007_data_flat070_original : block007_data_flat070 = (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) := by
  rw [block007_data_flat070_step]
def block007_data_flat071 : CoefficientMerge.Poly := [(nat_lit 253, Int.ofNat (nat_lit 262721401588008))]
theorem block007_data_flat071_step : block007_data_flat071 = (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) := by decide +kernel
theorem block007_data_flat071_original : block007_data_flat071 = (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) := by
  rw [block007_data_flat071_step]
def block007_data_flat072 : CoefficientMerge.Poly := [(nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat072_step : block007_data_flat072 = (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded) := by decide +kernel
theorem block007_data_flat072_original : block007_data_flat072 = (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded) := by
  rw [block007_data_flat072_step]
def block007_data_flat073 : CoefficientMerge.Poly := [(nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat073_step : block007_data_flat073 = (CoefficientMerge.fastMerge block007_data_flat071 block007_data_flat072) := by decide +kernel
theorem block007_data_flat073_original : block007_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded)) := by
  rw [block007_data_flat073_step, block007_data_flat071_original, block007_data_flat072_original]
def block007_data_flat074 : CoefficientMerge.Poly := [(nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat074_step : block007_data_flat074 = (CoefficientMerge.fastMerge block007_data_flat070 block007_data_flat073) := by decide +kernel
theorem block007_data_flat074_original : block007_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))) := by
  rw [block007_data_flat074_step, block007_data_flat070_original, block007_data_flat073_original]
def block007_data_flat075 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat075_step : block007_data_flat075 = (CoefficientMerge.fastMerge block007_data_flat069 block007_data_flat074) := by decide +kernel
theorem block007_data_flat075_original : block007_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded)))) := by
  rw [block007_data_flat075_step, block007_data_flat069_original, block007_data_flat074_original]
def block007_data_flat076 : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat076_step : block007_data_flat076 = (CoefficientMerge.fastMerge block007_data_flat066 block007_data_flat075) := by decide +kernel
theorem block007_data_flat076_original : block007_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))) := by
  rw [block007_data_flat076_step, block007_data_flat066_original, block007_data_flat075_original]
def block007_data_flat077 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996)), (nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat077_step : block007_data_flat077 = (CoefficientMerge.fastMerge block007_data_flat057 block007_data_flat076) := by decide +kernel
theorem block007_data_flat077_original : block007_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded)))))) := by
  rw [block007_data_flat077_step, block007_data_flat057_original, block007_data_flat076_original]
def block007_data_flat078 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800)), (nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400)), (nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996)), (nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408))]
theorem block007_data_flat078_step : block007_data_flat078 = (CoefficientMerge.fastMerge block007_data_flat038 block007_data_flat077) := by decide +kernel
theorem block007_data_flat078_original : block007_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))))) := by
  rw [block007_data_flat078_step, block007_data_flat038_original, block007_data_flat077_original]
def block007_data_flat079 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408))]
theorem block007_data_flat079_step : block007_data_flat079 = (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) := by decide +kernel
theorem block007_data_flat079_original : block007_data_flat079 = (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) := by
  rw [block007_data_flat079_step]
def block007_data_flat080 : CoefficientMerge.Poly := [(nat_lit 256, Int.ofNat (nat_lit 250651619416008))]
theorem block007_data_flat080_step : block007_data_flat080 = (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded) := by decide +kernel
theorem block007_data_flat080_original : block007_data_flat080 = (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded) := by
  rw [block007_data_flat080_step]
def block007_data_flat081 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008))]
theorem block007_data_flat081_step : block007_data_flat081 = (CoefficientMerge.fastMerge block007_data_flat079 block007_data_flat080) := by decide +kernel
theorem block007_data_flat081_original : block007_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) := by
  rw [block007_data_flat081_step, block007_data_flat079_original, block007_data_flat080_original]
def block007_data_flat082 : CoefficientMerge.Poly := [(nat_lit 257, Int.ofNat (nat_lit 255162297851208))]
theorem block007_data_flat082_step : block007_data_flat082 = (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) := by decide +kernel
theorem block007_data_flat082_original : block007_data_flat082 = (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) := by
  rw [block007_data_flat082_step]
def block007_data_flat083 : CoefficientMerge.Poly := [(nat_lit 258, Int.ofNat (nat_lit 276374549456676))]
theorem block007_data_flat083_step : block007_data_flat083 = (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) := by decide +kernel
theorem block007_data_flat083_original : block007_data_flat083 = (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) := by
  rw [block007_data_flat083_step]
def block007_data_flat084 : CoefficientMerge.Poly := [(nat_lit 259, Int.ofNat (nat_lit 224250703141212))]
theorem block007_data_flat084_step : block007_data_flat084 = (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded) := by decide +kernel
theorem block007_data_flat084_original : block007_data_flat084 = (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded) := by
  rw [block007_data_flat084_step]
def block007_data_flat085 : CoefficientMerge.Poly := [(nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212))]
theorem block007_data_flat085_step : block007_data_flat085 = (CoefficientMerge.fastMerge block007_data_flat083 block007_data_flat084) := by decide +kernel
theorem block007_data_flat085_original : block007_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)) := by
  rw [block007_data_flat085_step, block007_data_flat083_original, block007_data_flat084_original]
def block007_data_flat086 : CoefficientMerge.Poly := [(nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212))]
theorem block007_data_flat086_step : block007_data_flat086 = (CoefficientMerge.fastMerge block007_data_flat082 block007_data_flat085) := by decide +kernel
theorem block007_data_flat086_original : block007_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded))) := by
  rw [block007_data_flat086_step, block007_data_flat082_original, block007_data_flat085_original]
def block007_data_flat087 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212))]
theorem block007_data_flat087_step : block007_data_flat087 = (CoefficientMerge.fastMerge block007_data_flat081 block007_data_flat086) := by decide +kernel
theorem block007_data_flat087_original : block007_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) := by
  rw [block007_data_flat087_step, block007_data_flat081_original, block007_data_flat086_original]
def block007_data_flat088 : CoefficientMerge.Poly := [(nat_lit 260, Int.ofNat (nat_lit 202038123520332))]
theorem block007_data_flat088_step : block007_data_flat088 = (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) := by decide +kernel
theorem block007_data_flat088_original : block007_data_flat088 = (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) := by
  rw [block007_data_flat088_step]
def block007_data_flat089 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 157420230578820))]
theorem block007_data_flat089_step : block007_data_flat089 = (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded) := by decide +kernel
theorem block007_data_flat089_original : block007_data_flat089 = (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded) := by
  rw [block007_data_flat089_step]
def block007_data_flat090 : CoefficientMerge.Poly := [(nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820))]
theorem block007_data_flat090_step : block007_data_flat090 = (CoefficientMerge.fastMerge block007_data_flat088 block007_data_flat089) := by decide +kernel
theorem block007_data_flat090_original : block007_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) := by
  rw [block007_data_flat090_step, block007_data_flat088_original, block007_data_flat089_original]
def block007_data_flat091 : CoefficientMerge.Poly := [(nat_lit 262, Int.ofNat (nat_lit 149012007995340))]
theorem block007_data_flat091_step : block007_data_flat091 = (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) := by decide +kernel
theorem block007_data_flat091_original : block007_data_flat091 = (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) := by
  rw [block007_data_flat091_step]
def block007_data_flat092 : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 131646782756412))]
theorem block007_data_flat092_step : block007_data_flat092 = (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) := by decide +kernel
theorem block007_data_flat092_original : block007_data_flat092 = (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) := by
  rw [block007_data_flat092_step]
def block007_data_flat093 : CoefficientMerge.Poly := [(nat_lit 275, Int.ofNat (nat_lit 159353351125056))]
theorem block007_data_flat093_step : block007_data_flat093 = (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded) := by decide +kernel
theorem block007_data_flat093_original : block007_data_flat093 = (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded) := by
  rw [block007_data_flat093_step]
def block007_data_flat094 : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056))]
theorem block007_data_flat094_step : block007_data_flat094 = (CoefficientMerge.fastMerge block007_data_flat092 block007_data_flat093) := by decide +kernel
theorem block007_data_flat094_original : block007_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded)) := by
  rw [block007_data_flat094_step, block007_data_flat092_original, block007_data_flat093_original]
def block007_data_flat095 : CoefficientMerge.Poly := [(nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056))]
theorem block007_data_flat095_step : block007_data_flat095 = (CoefficientMerge.fastMerge block007_data_flat091 block007_data_flat094) := by decide +kernel
theorem block007_data_flat095_original : block007_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))) := by
  rw [block007_data_flat095_step, block007_data_flat091_original, block007_data_flat094_original]
def block007_data_flat096 : CoefficientMerge.Poly := [(nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056))]
theorem block007_data_flat096_step : block007_data_flat096 = (CoefficientMerge.fastMerge block007_data_flat090 block007_data_flat095) := by decide +kernel
theorem block007_data_flat096_original : block007_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded)))) := by
  rw [block007_data_flat096_step, block007_data_flat090_original, block007_data_flat095_original]
def block007_data_flat097 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056))]
theorem block007_data_flat097_step : block007_data_flat097 = (CoefficientMerge.fastMerge block007_data_flat087 block007_data_flat096) := by decide +kernel
theorem block007_data_flat097_original : block007_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) := by
  rw [block007_data_flat097_step, block007_data_flat087_original, block007_data_flat096_original]
def block007_data_flat098 : CoefficientMerge.Poly := [(nat_lit 276, Int.ofNat (nat_lit 325628128343232))]
theorem block007_data_flat098_step : block007_data_flat098 = (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) := by decide +kernel
theorem block007_data_flat098_original : block007_data_flat098 = (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) := by
  rw [block007_data_flat098_step]
def block007_data_flat099 : CoefficientMerge.Poly := [(nat_lit 277, Int.ofNat (nat_lit 285505542588816))]
theorem block007_data_flat099_step : block007_data_flat099 = (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded) := by decide +kernel
theorem block007_data_flat099_original : block007_data_flat099 = (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded) := by
  rw [block007_data_flat099_step]
def block007_data_flat100 : CoefficientMerge.Poly := [(nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816))]
theorem block007_data_flat100_step : block007_data_flat100 = (CoefficientMerge.fastMerge block007_data_flat098 block007_data_flat099) := by decide +kernel
theorem block007_data_flat100_original : block007_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) := by
  rw [block007_data_flat100_step, block007_data_flat098_original, block007_data_flat099_original]
def block007_data_flat101 : CoefficientMerge.Poly := [(nat_lit 278, Int.ofNat (nat_lit 253912851994032))]
theorem block007_data_flat101_step : block007_data_flat101 = (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) := by decide +kernel
theorem block007_data_flat101_original : block007_data_flat101 = (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) := by
  rw [block007_data_flat101_step]
def block007_data_flat102 : CoefficientMerge.Poly := [(nat_lit 279, Int.ofNat (nat_lit 256165050182832))]
theorem block007_data_flat102_step : block007_data_flat102 = (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) := by decide +kernel
theorem block007_data_flat102_original : block007_data_flat102 = (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) := by
  rw [block007_data_flat102_step]
def block007_data_flat103 : CoefficientMerge.Poly := [(nat_lit 280, Int.ofNat (nat_lit 262143636077232))]
theorem block007_data_flat103_step : block007_data_flat103 = (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded) := by decide +kernel
theorem block007_data_flat103_original : block007_data_flat103 = (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded) := by
  rw [block007_data_flat103_step]
def block007_data_flat104 : CoefficientMerge.Poly := [(nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232))]
theorem block007_data_flat104_step : block007_data_flat104 = (CoefficientMerge.fastMerge block007_data_flat102 block007_data_flat103) := by decide +kernel
theorem block007_data_flat104_original : block007_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)) := by
  rw [block007_data_flat104_step, block007_data_flat102_original, block007_data_flat103_original]
def block007_data_flat105 : CoefficientMerge.Poly := [(nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232))]
theorem block007_data_flat105_step : block007_data_flat105 = (CoefficientMerge.fastMerge block007_data_flat101 block007_data_flat104) := by decide +kernel
theorem block007_data_flat105_original : block007_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded))) := by
  rw [block007_data_flat105_step, block007_data_flat101_original, block007_data_flat104_original]
def block007_data_flat106 : CoefficientMerge.Poly := [(nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232))]
theorem block007_data_flat106_step : block007_data_flat106 = (CoefficientMerge.fastMerge block007_data_flat100 block007_data_flat105) := by decide +kernel
theorem block007_data_flat106_original : block007_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) := by
  rw [block007_data_flat106_step, block007_data_flat100_original, block007_data_flat105_original]
def block007_data_flat107 : CoefficientMerge.Poly := [(nat_lit 281, Int.ofNat (nat_lit 265639037357232))]
theorem block007_data_flat107_step : block007_data_flat107 = (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) := by decide +kernel
theorem block007_data_flat107_original : block007_data_flat107 = (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) := by
  rw [block007_data_flat107_step]
def block007_data_flat108 : CoefficientMerge.Poly := [(nat_lit 282, Int.ofNat (nat_lit 291518936774208))]
theorem block007_data_flat108_step : block007_data_flat108 = (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded) := by decide +kernel
theorem block007_data_flat108_original : block007_data_flat108 = (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded) := by
  rw [block007_data_flat108_step]
def block007_data_flat109 : CoefficientMerge.Poly := [(nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208))]
theorem block007_data_flat109_step : block007_data_flat109 = (CoefficientMerge.fastMerge block007_data_flat107 block007_data_flat108) := by decide +kernel
theorem block007_data_flat109_original : block007_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) := by
  rw [block007_data_flat109_step, block007_data_flat107_original, block007_data_flat108_original]
def block007_data_flat110 : CoefficientMerge.Poly := [(nat_lit 283, Int.ofNat (nat_lit 241024102148016))]
theorem block007_data_flat110_step : block007_data_flat110 = (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) := by decide +kernel
theorem block007_data_flat110_original : block007_data_flat110 = (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) := by
  rw [block007_data_flat110_step]
def block007_data_flat111 : CoefficientMerge.Poly := [(nat_lit 284, Int.ofNat (nat_lit 231218915577408))]
theorem block007_data_flat111_step : block007_data_flat111 = (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) := by decide +kernel
theorem block007_data_flat111_original : block007_data_flat111 = (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) := by
  rw [block007_data_flat111_step]
def block007_data_flat112 : CoefficientMerge.Poly := [(nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat112_step : block007_data_flat112 = (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded) := by decide +kernel
theorem block007_data_flat112_original : block007_data_flat112 = (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded) := by
  rw [block007_data_flat112_step]
def block007_data_flat113 : CoefficientMerge.Poly := [(nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat113_step : block007_data_flat113 = (CoefficientMerge.fastMerge block007_data_flat111 block007_data_flat112) := by decide +kernel
theorem block007_data_flat113_original : block007_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)) := by
  rw [block007_data_flat113_step, block007_data_flat111_original, block007_data_flat112_original]
def block007_data_flat114 : CoefficientMerge.Poly := [(nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat114_step : block007_data_flat114 = (CoefficientMerge.fastMerge block007_data_flat110 block007_data_flat113) := by decide +kernel
theorem block007_data_flat114_original : block007_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded))) := by
  rw [block007_data_flat114_step, block007_data_flat110_original, block007_data_flat113_original]
def block007_data_flat115 : CoefficientMerge.Poly := [(nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat115_step : block007_data_flat115 = (CoefficientMerge.fastMerge block007_data_flat109 block007_data_flat114) := by decide +kernel
theorem block007_data_flat115_original : block007_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))) := by
  rw [block007_data_flat115_step, block007_data_flat109_original, block007_data_flat114_original]
def block007_data_flat116 : CoefficientMerge.Poly := [(nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat116_step : block007_data_flat116 = (CoefficientMerge.fastMerge block007_data_flat106 block007_data_flat115) := by decide +kernel
theorem block007_data_flat116_original : block007_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded))))) := by
  rw [block007_data_flat116_step, block007_data_flat106_original, block007_data_flat115_original]
def block007_data_flat117 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056)), (nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584))]
theorem block007_data_flat117_step : block007_data_flat117 = (CoefficientMerge.fastMerge block007_data_flat097 block007_data_flat116) := by decide +kernel
theorem block007_data_flat117_original : block007_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) := by
  rw [block007_data_flat117_step, block007_data_flat097_original, block007_data_flat116_original]
def block007_data_flat118 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 166489350215040))]
theorem block007_data_flat118_step : block007_data_flat118 = (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) := by decide +kernel
theorem block007_data_flat118_original : block007_data_flat118 = (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) := by
  rw [block007_data_flat118_step]
def block007_data_flat119 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 159211799569152))]
theorem block007_data_flat119_step : block007_data_flat119 = (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded) := by decide +kernel
theorem block007_data_flat119_original : block007_data_flat119 = (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded) := by
  rw [block007_data_flat119_step]
def block007_data_flat120 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152))]
theorem block007_data_flat120_step : block007_data_flat120 = (CoefficientMerge.fastMerge block007_data_flat118 block007_data_flat119) := by decide +kernel
theorem block007_data_flat120_original : block007_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) := by
  rw [block007_data_flat120_step, block007_data_flat118_original, block007_data_flat119_original]
def block007_data_flat121 : CoefficientMerge.Poly := [(nat_lit 300, Int.ofNat (nat_lit 204859561585536))]
theorem block007_data_flat121_step : block007_data_flat121 = (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) := by decide +kernel
theorem block007_data_flat121_original : block007_data_flat121 = (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) := by
  rw [block007_data_flat121_step]
def block007_data_flat122 : CoefficientMerge.Poly := [(nat_lit 301, Int.ofNat (nat_lit 363727996258176))]
theorem block007_data_flat122_step : block007_data_flat122 = (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) := by decide +kernel
theorem block007_data_flat122_original : block007_data_flat122 = (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) := by
  rw [block007_data_flat122_step]
def block007_data_flat123 : CoefficientMerge.Poly := [(nat_lit 302, Int.ofNat (nat_lit 314919946272096))]
theorem block007_data_flat123_step : block007_data_flat123 = (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded) := by decide +kernel
theorem block007_data_flat123_original : block007_data_flat123 = (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded) := by
  rw [block007_data_flat123_step]
def block007_data_flat124 : CoefficientMerge.Poly := [(nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096))]
theorem block007_data_flat124_step : block007_data_flat124 = (CoefficientMerge.fastMerge block007_data_flat122 block007_data_flat123) := by decide +kernel
theorem block007_data_flat124_original : block007_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)) := by
  rw [block007_data_flat124_step, block007_data_flat122_original, block007_data_flat123_original]
def block007_data_flat125 : CoefficientMerge.Poly := [(nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096))]
theorem block007_data_flat125_step : block007_data_flat125 = (CoefficientMerge.fastMerge block007_data_flat121 block007_data_flat124) := by decide +kernel
theorem block007_data_flat125_original : block007_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded))) := by
  rw [block007_data_flat125_step, block007_data_flat121_original, block007_data_flat124_original]
def block007_data_flat126 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096))]
theorem block007_data_flat126_step : block007_data_flat126 = (CoefficientMerge.fastMerge block007_data_flat120 block007_data_flat125) := by decide +kernel
theorem block007_data_flat126_original : block007_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) := by
  rw [block007_data_flat126_step, block007_data_flat120_original, block007_data_flat125_original]
def block007_data_flat127 : CoefficientMerge.Poly := [(nat_lit 303, Int.ofNat (nat_lit 314422158328992))]
theorem block007_data_flat127_step : block007_data_flat127 = (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) := by decide +kernel
theorem block007_data_flat127_original : block007_data_flat127 = (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) := by
  rw [block007_data_flat127_step]
def block007_data_flat128 : CoefficientMerge.Poly := [(nat_lit 304, Int.ofNat (nat_lit 319130318882592))]
theorem block007_data_flat128_step : block007_data_flat128 = (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded) := by decide +kernel
theorem block007_data_flat128_original : block007_data_flat128 = (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded) := by
  rw [block007_data_flat128_step]
def block007_data_flat129 : CoefficientMerge.Poly := [(nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592))]
theorem block007_data_flat129_step : block007_data_flat129 = (CoefficientMerge.fastMerge block007_data_flat127 block007_data_flat128) := by decide +kernel
theorem block007_data_flat129_original : block007_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) := by
  rw [block007_data_flat129_step, block007_data_flat127_original, block007_data_flat128_original]
def block007_data_flat130 : CoefficientMerge.Poly := [(nat_lit 305, Int.ofNat (nat_lit 321355294821792))]
theorem block007_data_flat130_step : block007_data_flat130 = (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) := by decide +kernel
theorem block007_data_flat130_original : block007_data_flat130 = (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) := by
  rw [block007_data_flat130_step]
def block007_data_flat131 : CoefficientMerge.Poly := [(nat_lit 306, Int.ofNat (nat_lit 352380815538048))]
theorem block007_data_flat131_step : block007_data_flat131 = (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) := by decide +kernel
theorem block007_data_flat131_original : block007_data_flat131 = (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) := by
  rw [block007_data_flat131_step]
def block007_data_flat132 : CoefficientMerge.Poly := [(nat_lit 307, Int.ofNat (nat_lit 291890417851296))]
theorem block007_data_flat132_step : block007_data_flat132 = (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded) := by decide +kernel
theorem block007_data_flat132_original : block007_data_flat132 = (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded) := by
  rw [block007_data_flat132_step]
def block007_data_flat133 : CoefficientMerge.Poly := [(nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296))]
theorem block007_data_flat133_step : block007_data_flat133 = (CoefficientMerge.fastMerge block007_data_flat131 block007_data_flat132) := by decide +kernel
theorem block007_data_flat133_original : block007_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded)) := by
  rw [block007_data_flat133_step, block007_data_flat131_original, block007_data_flat132_original]
def block007_data_flat134 : CoefficientMerge.Poly := [(nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296))]
theorem block007_data_flat134_step : block007_data_flat134 = (CoefficientMerge.fastMerge block007_data_flat130 block007_data_flat133) := by decide +kernel
theorem block007_data_flat134_original : block007_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))) := by
  rw [block007_data_flat134_step, block007_data_flat130_original, block007_data_flat133_original]
def block007_data_flat135 : CoefficientMerge.Poly := [(nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296))]
theorem block007_data_flat135_step : block007_data_flat135 = (CoefficientMerge.fastMerge block007_data_flat129 block007_data_flat134) := by decide +kernel
theorem block007_data_flat135_original : block007_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded)))) := by
  rw [block007_data_flat135_step, block007_data_flat129_original, block007_data_flat134_original]
def block007_data_flat136 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296))]
theorem block007_data_flat136_step : block007_data_flat136 = (CoefficientMerge.fastMerge block007_data_flat126 block007_data_flat135) := by decide +kernel
theorem block007_data_flat136_original : block007_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) := by
  rw [block007_data_flat136_step, block007_data_flat126_original, block007_data_flat135_original]
def block007_data_flat137 : CoefficientMerge.Poly := [(nat_lit 308, Int.ofNat (nat_lit 294121979826048))]
theorem block007_data_flat137_step : block007_data_flat137 = (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) := by decide +kernel
theorem block007_data_flat137_original : block007_data_flat137 = (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) := by
  rw [block007_data_flat137_step]
def block007_data_flat138 : CoefficientMerge.Poly := [(nat_lit 309, Int.ofNat (nat_lit 232524785759904))]
theorem block007_data_flat138_step : block007_data_flat138 = (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded) := by decide +kernel
theorem block007_data_flat138_original : block007_data_flat138 = (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded) := by
  rw [block007_data_flat138_step]
def block007_data_flat139 : CoefficientMerge.Poly := [(nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904))]
theorem block007_data_flat139_step : block007_data_flat139 = (CoefficientMerge.fastMerge block007_data_flat137 block007_data_flat138) := by decide +kernel
theorem block007_data_flat139_original : block007_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) := by
  rw [block007_data_flat139_step, block007_data_flat137_original, block007_data_flat138_original]
def block007_data_flat140 : CoefficientMerge.Poly := [(nat_lit 310, Int.ofNat (nat_lit 163964446295040))]
theorem block007_data_flat140_step : block007_data_flat140 = (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) := by decide +kernel
theorem block007_data_flat140_original : block007_data_flat140 = (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) := by
  rw [block007_data_flat140_step]
def block007_data_flat141 : CoefficientMerge.Poly := [(nat_lit 311, Int.ofNat (nat_lit 152337682202112))]
theorem block007_data_flat141_step : block007_data_flat141 = (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) := by decide +kernel
theorem block007_data_flat141_original : block007_data_flat141 = (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) := by
  rw [block007_data_flat141_step]
def block007_data_flat142 : CoefficientMerge.Poly := [(nat_lit 325, Int.ofNat (nat_lit 197453219040000))]
theorem block007_data_flat142_step : block007_data_flat142 = (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded) := by decide +kernel
theorem block007_data_flat142_original : block007_data_flat142 = (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded) := by
  rw [block007_data_flat142_step]
def block007_data_flat143 : CoefficientMerge.Poly := [(nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000))]
theorem block007_data_flat143_step : block007_data_flat143 = (CoefficientMerge.fastMerge block007_data_flat141 block007_data_flat142) := by decide +kernel
theorem block007_data_flat143_original : block007_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)) := by
  rw [block007_data_flat143_step, block007_data_flat141_original, block007_data_flat142_original]
def block007_data_flat144 : CoefficientMerge.Poly := [(nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000))]
theorem block007_data_flat144_step : block007_data_flat144 = (CoefficientMerge.fastMerge block007_data_flat140 block007_data_flat143) := by decide +kernel
theorem block007_data_flat144_original : block007_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded))) := by
  rw [block007_data_flat144_step, block007_data_flat140_original, block007_data_flat143_original]
def block007_data_flat145 : CoefficientMerge.Poly := [(nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000))]
theorem block007_data_flat145_step : block007_data_flat145 = (CoefficientMerge.fastMerge block007_data_flat139 block007_data_flat144) := by decide +kernel
theorem block007_data_flat145_original : block007_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) := by
  rw [block007_data_flat145_step, block007_data_flat139_original, block007_data_flat144_original]
def block007_data_flat146 : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 339075700064640))]
theorem block007_data_flat146_step : block007_data_flat146 = (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) := by decide +kernel
theorem block007_data_flat146_original : block007_data_flat146 = (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) := by
  rw [block007_data_flat146_step]
def block007_data_flat147 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 310411363872960))]
theorem block007_data_flat147_step : block007_data_flat147 = (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded) := by decide +kernel
theorem block007_data_flat147_original : block007_data_flat147 = (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded) := by
  rw [block007_data_flat147_step]
def block007_data_flat148 : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960))]
theorem block007_data_flat148_step : block007_data_flat148 = (CoefficientMerge.fastMerge block007_data_flat146 block007_data_flat147) := by decide +kernel
theorem block007_data_flat148_original : block007_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) := by
  rw [block007_data_flat148_step, block007_data_flat146_original, block007_data_flat147_original]
def block007_data_flat149 : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 310881610468800))]
theorem block007_data_flat149_step : block007_data_flat149 = (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) := by decide +kernel
theorem block007_data_flat149_original : block007_data_flat149 = (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) := by
  rw [block007_data_flat149_step]
def block007_data_flat150 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 311581012881600))]
theorem block007_data_flat150_step : block007_data_flat150 = (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) := by decide +kernel
theorem block007_data_flat150_original : block007_data_flat150 = (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) := by
  rw [block007_data_flat150_step]
def block007_data_flat151 : CoefficientMerge.Poly := [(nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat151_step : block007_data_flat151 = (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded) := by decide +kernel
theorem block007_data_flat151_original : block007_data_flat151 = (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded) := by
  rw [block007_data_flat151_step]
def block007_data_flat152 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat152_step : block007_data_flat152 = (CoefficientMerge.fastMerge block007_data_flat150 block007_data_flat151) := by decide +kernel
theorem block007_data_flat152_original : block007_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)) := by
  rw [block007_data_flat152_step, block007_data_flat150_original, block007_data_flat151_original]
def block007_data_flat153 : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat153_step : block007_data_flat153 = (CoefficientMerge.fastMerge block007_data_flat149 block007_data_flat152) := by decide +kernel
theorem block007_data_flat153_original : block007_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded))) := by
  rw [block007_data_flat153_step, block007_data_flat149_original, block007_data_flat152_original]
def block007_data_flat154 : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat154_step : block007_data_flat154 = (CoefficientMerge.fastMerge block007_data_flat148 block007_data_flat153) := by decide +kernel
theorem block007_data_flat154_original : block007_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)))) := by
  rw [block007_data_flat154_step, block007_data_flat148_original, block007_data_flat153_original]
def block007_data_flat155 : CoefficientMerge.Poly := [(nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat155_step : block007_data_flat155 = (CoefficientMerge.fastMerge block007_data_flat145 block007_data_flat154) := by decide +kernel
theorem block007_data_flat155_original : block007_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded))))) := by
  rw [block007_data_flat155_step, block007_data_flat145_original, block007_data_flat154_original]
def block007_data_flat156 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296)), (nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat156_step : block007_data_flat156 = (CoefficientMerge.fastMerge block007_data_flat136 block007_data_flat155) := by decide +kernel
theorem block007_data_flat156_original : block007_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)))))) := by
  rw [block007_data_flat156_step, block007_data_flat136_original, block007_data_flat155_original]
def block007_data_flat157 : CoefficientMerge.Poly := [(nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056)), (nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584)), (nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296)), (nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat157_step : block007_data_flat157 = (CoefficientMerge.fastMerge block007_data_flat117 block007_data_flat156) := by decide +kernel
theorem block007_data_flat157_original : block007_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded))))))) := by
  rw [block007_data_flat157_step, block007_data_flat117_original, block007_data_flat156_original]
def block007_data_flat158 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800)), (nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400)), (nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996)), (nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408)), (nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056)), (nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584)), (nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296)), (nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat158_step : block007_data_flat158 = (CoefficientMerge.fastMerge block007_data_flat078 block007_data_flat157) := by decide +kernel
theorem block007_data_flat158_original : block007_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)))))))) := by
  rw [block007_data_flat158_step, block007_data_flat078_original, block007_data_flat157_original]
def block007_data_flat159 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 145973111961600)), (nat_lit 189, Int.ofNat (nat_lit 91276900915200)), (nat_lit 190, Int.ofNat (nat_lit 101070199171200)), (nat_lit 191, Int.ofNat (nat_lit 66423577651200)), (nat_lit 200, Int.ofNat (nat_lit 130635871027200)), (nat_lit 201, Int.ofNat (nat_lit 238603162254336)), (nat_lit 202, Int.ofNat (nat_lit 205050002305500)), (nat_lit 203, Int.ofNat (nat_lit 206244770071032)), (nat_lit 204, Int.ofNat (nat_lit 254087646219792)), (nat_lit 205, Int.ofNat (nat_lit 238680835192800)), (nat_lit 206, Int.ofNat (nat_lit 216844064236800)), (nat_lit 207, Int.ofNat (nat_lit 222147409478400)), (nat_lit 208, Int.ofNat (nat_lit 230406382281600)), (nat_lit 209, Int.ofNat (nat_lit 236182170470400)), (nat_lit 210, Int.ofNat (nat_lit 254053174636800)), (nat_lit 211, Int.ofNat (nat_lit 193981723689600)), (nat_lit 212, Int.ofNat (nat_lit 155076940972800)), (nat_lit 213, Int.ofNat (nat_lit 102043327478400)), (nat_lit 214, Int.ofNat (nat_lit 111957702998400)), (nat_lit 215, Int.ofNat (nat_lit 77432158742400)), (nat_lit 225, Int.ofNat (nat_lit 144531443713536)), (nat_lit 226, Int.ofNat (nat_lit 253532085092352)), (nat_lit 227, Int.ofNat (nat_lit 229630294124352)), (nat_lit 228, Int.ofNat (nat_lit 266810264348760)), (nat_lit 229, Int.ofNat (nat_lit 250127712393768)), (nat_lit 230, Int.ofNat (nat_lit 227785960653768)), (nat_lit 231, Int.ofNat (nat_lit 232584325111368)), (nat_lit 232, Int.ofNat (nat_lit 240338317130568)), (nat_lit 233, Int.ofNat (nat_lit 245609124535368)), (nat_lit 234, Int.ofNat (nat_lit 264258199992996)), (nat_lit 235, Int.ofNat (nat_lit 206247872412252)), (nat_lit 236, Int.ofNat (nat_lit 170868583296972)), (nat_lit 237, Int.ofNat (nat_lit 120997827084420)), (nat_lit 238, Int.ofNat (nat_lit 126521758552140)), (nat_lit 239, Int.ofNat (nat_lit 96623441813052)), (nat_lit 250, Int.ofNat (nat_lit 145564793865216)), (nat_lit 251, Int.ofNat (nat_lit 266333360622912)), (nat_lit 252, Int.ofNat (nat_lit 281629959463512)), (nat_lit 253, Int.ofNat (nat_lit 262721401588008)), (nat_lit 254, Int.ofNat (nat_lit 239619520878408)), (nat_lit 255, Int.ofNat (nat_lit 243657756366408)), (nat_lit 256, Int.ofNat (nat_lit 250651619416008)), (nat_lit 257, Int.ofNat (nat_lit 255162297851208)), (nat_lit 258, Int.ofNat (nat_lit 276374549456676)), (nat_lit 259, Int.ofNat (nat_lit 224250703141212)), (nat_lit 260, Int.ofNat (nat_lit 202038123520332)), (nat_lit 261, Int.ofNat (nat_lit 157420230578820)), (nat_lit 262, Int.ofNat (nat_lit 149012007995340)), (nat_lit 263, Int.ofNat (nat_lit 131646782756412)), (nat_lit 275, Int.ofNat (nat_lit 159353351125056)), (nat_lit 276, Int.ofNat (nat_lit 325628128343232)), (nat_lit 277, Int.ofNat (nat_lit 285505542588816)), (nat_lit 278, Int.ofNat (nat_lit 253912851994032)), (nat_lit 279, Int.ofNat (nat_lit 256165050182832)), (nat_lit 280, Int.ofNat (nat_lit 262143636077232)), (nat_lit 281, Int.ofNat (nat_lit 265639037357232)), (nat_lit 282, Int.ofNat (nat_lit 291518936774208)), (nat_lit 283, Int.ofNat (nat_lit 241024102148016)), (nat_lit 284, Int.ofNat (nat_lit 231218915577408)), (nat_lit 285, Int.ofNat (nat_lit 188817502897584)), (nat_lit 286, Int.ofNat (nat_lit 166489350215040)), (nat_lit 287, Int.ofNat (nat_lit 159211799569152)), (nat_lit 300, Int.ofNat (nat_lit 204859561585536)), (nat_lit 301, Int.ofNat (nat_lit 363727996258176)), (nat_lit 302, Int.ofNat (nat_lit 314919946272096)), (nat_lit 303, Int.ofNat (nat_lit 314422158328992)), (nat_lit 304, Int.ofNat (nat_lit 319130318882592)), (nat_lit 305, Int.ofNat (nat_lit 321355294821792)), (nat_lit 306, Int.ofNat (nat_lit 352380815538048)), (nat_lit 307, Int.ofNat (nat_lit 291890417851296)), (nat_lit 308, Int.ofNat (nat_lit 294121979826048)), (nat_lit 309, Int.ofNat (nat_lit 232524785759904)), (nat_lit 310, Int.ofNat (nat_lit 163964446295040)), (nat_lit 311, Int.ofNat (nat_lit 152337682202112)), (nat_lit 325, Int.ofNat (nat_lit 197453219040000)), (nat_lit 326, Int.ofNat (nat_lit 339075700064640)), (nat_lit 327, Int.ofNat (nat_lit 310411363872960)), (nat_lit 328, Int.ofNat (nat_lit 310881610468800)), (nat_lit 329, Int.ofNat (nat_lit 311581012881600)), (nat_lit 330, Int.ofNat (nat_lit 340076468793600))]
theorem block007_data_flat159_step : block007_data_flat159 = (CoefficientMerge.trim block007_data_flat158) := by decide +kernel
theorem block007_data_flat159_original : block007_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded))))))))) := by
  rw [block007_data_flat159_step, block007_data_flat158_original]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)))))))) := by
  have h : block007 = block007_data_flat159 := by decide +kernel
  exact h.trans block007_data_flat159_original
theorem block007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0369Coded_nonneg g hg hA hB) (atom0370Coded_nonneg g hg hA hB)) (add_nonneg (atom0371Coded_nonneg g hg hA hB) (add_nonneg (atom0372Coded_nonneg g hg hA hB) (atom0373Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0374Coded_nonneg g hg hA hB) (atom0375Coded_nonneg g hg hA hB)) (add_nonneg (atom0376Coded_nonneg g hg hA hB) (add_nonneg (atom0377Coded_nonneg g hg hA hB) (atom0378Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0379Coded_nonneg g hg hA hB) (atom0380Coded_nonneg g hg hA hB)) (add_nonneg (atom0381Coded_nonneg g hg hA hB) (add_nonneg (atom0382Coded_nonneg g hg hA hB) (atom0383Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0384Coded_nonneg g hg hA hB) (atom0385Coded_nonneg g hg hA hB)) (add_nonneg (atom0386Coded_nonneg g hg hA hB) (add_nonneg (atom0387Coded_nonneg g hg hA hB) (atom0388Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0389Coded_nonneg g hg hA hB) (atom0390Coded_nonneg g hg hA hB)) (add_nonneg (atom0391Coded_nonneg g hg hA hB) (add_nonneg (atom0392Coded_nonneg g hg hA hB) (atom0393Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0394Coded_nonneg g hg hA hB) (atom0395Coded_nonneg g hg hA hB)) (add_nonneg (atom0396Coded_nonneg g hg hA hB) (add_nonneg (atom0397Coded_nonneg g hg hA hB) (atom0398Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0399Coded_nonneg g hg hA hB) (atom0400Coded_nonneg g hg hA hB)) (add_nonneg (atom0401Coded_nonneg g hg hA hB) (add_nonneg (atom0402Coded_nonneg g hg hA hB) (atom0403Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0404Coded_nonneg g hg hA hB) (atom0405Coded_nonneg g hg hA hB)) (add_nonneg (atom0406Coded_nonneg g hg hA hB) (add_nonneg (atom0407Coded_nonneg g hg hA hB) (atom0408Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0409Coded_nonneg g hg hA hB) (atom0410Coded_nonneg g hg hA hB)) (add_nonneg (atom0411Coded_nonneg g hg hA hB) (add_nonneg (atom0412Coded_nonneg g hg hA hB) (atom0413Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0414Coded_nonneg g hg hA hB) (atom0415Coded_nonneg g hg hA hB)) (add_nonneg (atom0416Coded_nonneg g hg hA hB) (add_nonneg (atom0417Coded_nonneg g hg hA hB) (atom0418Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0419Coded_nonneg g hg hA hB) (atom0420Coded_nonneg g hg hA hB)) (add_nonneg (atom0421Coded_nonneg g hg hA hB) (add_nonneg (atom0422Coded_nonneg g hg hA hB) (atom0423Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0424Coded_nonneg g hg hA hB) (atom0425Coded_nonneg g hg hA hB)) (add_nonneg (atom0426Coded_nonneg g hg hA hB) (add_nonneg (atom0427Coded_nonneg g hg hA hB) (atom0428Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0429Coded_nonneg g hg hA hB) (atom0430Coded_nonneg g hg hA hB)) (add_nonneg (atom0431Coded_nonneg g hg hA hB) (add_nonneg (atom0432Coded_nonneg g hg hA hB) (atom0433Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0434Coded_nonneg g hg hA hB) (atom0435Coded_nonneg g hg hA hB)) (add_nonneg (atom0436Coded_nonneg g hg hA hB) (add_nonneg (atom0437Coded_nonneg g hg hA hB) (atom0438Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0439Coded_nonneg g hg hA hB) (atom0440Coded_nonneg g hg hA hB)) (add_nonneg (atom0441Coded_nonneg g hg hA hB) (add_nonneg (atom0442Coded_nonneg g hg hA hB) (atom0443Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0444Coded_nonneg g hg hA hB) (atom0445Coded_nonneg g hg hA hB)) (add_nonneg (atom0446Coded_nonneg g hg hA hB) (add_nonneg (atom0447Coded_nonneg g hg hA hB) (atom0448Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
