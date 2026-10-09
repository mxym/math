import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0369 : SparsePolynomial.Poly := [([0,7,20], 1)]
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
def atom0369Coded : CoefficientMerge.Poly := [(188, 1)]
theorem atom0369Coded_decode : atom0369 = SparsePolynomial.decodeCubic 24 atom0369Coded := by decide +kernel
theorem atom0369Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) := by
  have h := atom0369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0370 : SparsePolynomial.Poly := [([0,7,21], 1)]
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
def atom0370Coded : CoefficientMerge.Poly := [(189, 1)]
theorem atom0370Coded_decode : atom0370 = SparsePolynomial.decodeCubic 24 atom0370Coded := by decide +kernel
theorem atom0370Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded) := by
  have h := atom0370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0371 : SparsePolynomial.Poly := [([0,7,22], 1)]
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
def atom0371Coded : CoefficientMerge.Poly := [(190, 1)]
theorem atom0371Coded_decode : atom0371 = SparsePolynomial.decodeCubic 24 atom0371Coded := by decide +kernel
theorem atom0371Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) := by
  have h := atom0371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0372 : SparsePolynomial.Poly := [([0,7,23], 1)]
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
def atom0372Coded : CoefficientMerge.Poly := [(191, 1)]
theorem atom0372Coded_decode : atom0372 = SparsePolynomial.decodeCubic 24 atom0372Coded := by decide +kernel
theorem atom0372Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) := by
  have h := atom0372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0373 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130635871027200 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373Coded : CoefficientMerge.Poly := [(200, 1)]
theorem atom0373Coded_decode : atom0373 = SparsePolynomial.decodeCubic 24 atom0373Coded := by decide +kernel
theorem atom0373Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded) := by
  have h := atom0373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0374 : SparsePolynomial.Poly := [([0,8,9], 1)]
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
def atom0374Coded : CoefficientMerge.Poly := [(201, 1)]
theorem atom0374Coded_decode : atom0374 = SparsePolynomial.decodeCubic 24 atom0374Coded := by decide +kernel
theorem atom0374Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) := by
  have h := atom0374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0375 : SparsePolynomial.Poly := [([0,8,10], 1)]
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
def atom0375Coded : CoefficientMerge.Poly := [(202, 1)]
theorem atom0375Coded_decode : atom0375 = SparsePolynomial.decodeCubic 24 atom0375Coded := by decide +kernel
theorem atom0375Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded) := by
  have h := atom0375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0376 : SparsePolynomial.Poly := [([0,8,11], 1)]
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
def atom0376Coded : CoefficientMerge.Poly := [(203, 1)]
theorem atom0376Coded_decode : atom0376 = SparsePolynomial.decodeCubic 24 atom0376Coded := by decide +kernel
theorem atom0376Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) := by
  have h := atom0376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0377 : SparsePolynomial.Poly := [([0,8,12], 1)]
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
def atom0377Coded : CoefficientMerge.Poly := [(204, 1)]
theorem atom0377Coded_decode : atom0377 = SparsePolynomial.decodeCubic 24 atom0377Coded := by decide +kernel
theorem atom0377Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) := by
  have h := atom0377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0378 : SparsePolynomial.Poly := [([0,8,13], 1)]
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
def atom0378Coded : CoefficientMerge.Poly := [(205, 1)]
theorem atom0378Coded_decode : atom0378 = SparsePolynomial.decodeCubic 24 atom0378Coded := by decide +kernel
theorem atom0378Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded) := by
  have h := atom0378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0379 : SparsePolynomial.Poly := [([0,8,14], 1)]
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
def atom0379Coded : CoefficientMerge.Poly := [(206, 1)]
theorem atom0379Coded_decode : atom0379 = SparsePolynomial.decodeCubic 24 atom0379Coded := by decide +kernel
theorem atom0379Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) := by
  have h := atom0379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0380 : SparsePolynomial.Poly := [([0,8,15], 1)]
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
def atom0380Coded : CoefficientMerge.Poly := [(207, 1)]
theorem atom0380Coded_decode : atom0380 = SparsePolynomial.decodeCubic 24 atom0380Coded := by decide +kernel
theorem atom0380Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded) := by
  have h := atom0380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0381 : SparsePolynomial.Poly := [([0,8,16], 1)]
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
def atom0381Coded : CoefficientMerge.Poly := [(208, 1)]
theorem atom0381Coded_decode : atom0381 = SparsePolynomial.decodeCubic 24 atom0381Coded := by decide +kernel
theorem atom0381Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) := by
  have h := atom0381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0382 : SparsePolynomial.Poly := [([0,8,17], 1)]
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
def atom0382Coded : CoefficientMerge.Poly := [(209, 1)]
theorem atom0382Coded_decode : atom0382 = SparsePolynomial.decodeCubic 24 atom0382Coded := by decide +kernel
theorem atom0382Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) := by
  have h := atom0382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0383 : SparsePolynomial.Poly := [([0,8,18], 1)]
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
def atom0383Coded : CoefficientMerge.Poly := [(210, 1)]
theorem atom0383Coded_decode : atom0383 = SparsePolynomial.decodeCubic 24 atom0383Coded := by decide +kernel
theorem atom0383Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded) := by
  have h := atom0383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0384 : SparsePolynomial.Poly := [([0,8,19], 1)]
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
def atom0384Coded : CoefficientMerge.Poly := [(211, 1)]
theorem atom0384Coded_decode : atom0384 = SparsePolynomial.decodeCubic 24 atom0384Coded := by decide +kernel
theorem atom0384Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) := by
  have h := atom0384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0385 : SparsePolynomial.Poly := [([0,8,20], 1)]
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
def atom0385Coded : CoefficientMerge.Poly := [(212, 1)]
theorem atom0385Coded_decode : atom0385 = SparsePolynomial.decodeCubic 24 atom0385Coded := by decide +kernel
theorem atom0385Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded) := by
  have h := atom0385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0386 : SparsePolynomial.Poly := [([0,8,21], 1)]
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
def atom0386Coded : CoefficientMerge.Poly := [(213, 1)]
theorem atom0386Coded_decode : atom0386 = SparsePolynomial.decodeCubic 24 atom0386Coded := by decide +kernel
theorem atom0386Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) := by
  have h := atom0386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0387 : SparsePolynomial.Poly := [([0,8,22], 1)]
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
def atom0387Coded : CoefficientMerge.Poly := [(214, 1)]
theorem atom0387Coded_decode : atom0387 = SparsePolynomial.decodeCubic 24 atom0387Coded := by decide +kernel
theorem atom0387Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) := by
  have h := atom0387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0388 : SparsePolynomial.Poly := [([0,8,23], 1)]
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
def atom0388Coded : CoefficientMerge.Poly := [(215, 1)]
theorem atom0388Coded_decode : atom0388 = SparsePolynomial.decodeCubic 24 atom0388Coded := by decide +kernel
theorem atom0388Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded) := by
  have h := atom0388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0389 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144531443713536 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389Coded : CoefficientMerge.Poly := [(225, 1)]
theorem atom0389Coded_decode : atom0389 = SparsePolynomial.decodeCubic 24 atom0389Coded := by decide +kernel
theorem atom0389Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) := by
  have h := atom0389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0390 : SparsePolynomial.Poly := [([0,9,10], 1)]
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
def atom0390Coded : CoefficientMerge.Poly := [(226, 1)]
theorem atom0390Coded_decode : atom0390 = SparsePolynomial.decodeCubic 24 atom0390Coded := by decide +kernel
theorem atom0390Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded) := by
  have h := atom0390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0391 : SparsePolynomial.Poly := [([0,9,11], 1)]
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
def atom0391Coded : CoefficientMerge.Poly := [(227, 1)]
theorem atom0391Coded_decode : atom0391 = SparsePolynomial.decodeCubic 24 atom0391Coded := by decide +kernel
theorem atom0391Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) := by
  have h := atom0391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0392 : SparsePolynomial.Poly := [([0,9,12], 1)]
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
def atom0392Coded : CoefficientMerge.Poly := [(228, 1)]
theorem atom0392Coded_decode : atom0392 = SparsePolynomial.decodeCubic 24 atom0392Coded := by decide +kernel
theorem atom0392Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) := by
  have h := atom0392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0393 : SparsePolynomial.Poly := [([0,9,13], 1)]
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
def atom0393Coded : CoefficientMerge.Poly := [(229, 1)]
theorem atom0393Coded_decode : atom0393 = SparsePolynomial.decodeCubic 24 atom0393Coded := by decide +kernel
theorem atom0393Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded) := by
  have h := atom0393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0394 : SparsePolynomial.Poly := [([0,9,14], 1)]
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
def atom0394Coded : CoefficientMerge.Poly := [(230, 1)]
theorem atom0394Coded_decode : atom0394 = SparsePolynomial.decodeCubic 24 atom0394Coded := by decide +kernel
theorem atom0394Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) := by
  have h := atom0394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0395 : SparsePolynomial.Poly := [([0,9,15], 1)]
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
def atom0395Coded : CoefficientMerge.Poly := [(231, 1)]
theorem atom0395Coded_decode : atom0395 = SparsePolynomial.decodeCubic 24 atom0395Coded := by decide +kernel
theorem atom0395Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded) := by
  have h := atom0395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0396 : SparsePolynomial.Poly := [([0,9,16], 1)]
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
def atom0396Coded : CoefficientMerge.Poly := [(232, 1)]
theorem atom0396Coded_decode : atom0396 = SparsePolynomial.decodeCubic 24 atom0396Coded := by decide +kernel
theorem atom0396Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) := by
  have h := atom0396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0397 : SparsePolynomial.Poly := [([0,9,17], 1)]
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
def atom0397Coded : CoefficientMerge.Poly := [(233, 1)]
theorem atom0397Coded_decode : atom0397 = SparsePolynomial.decodeCubic 24 atom0397Coded := by decide +kernel
theorem atom0397Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) := by
  have h := atom0397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0398 : SparsePolynomial.Poly := [([0,9,18], 1)]
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
def atom0398Coded : CoefficientMerge.Poly := [(234, 1)]
theorem atom0398Coded_decode : atom0398 = SparsePolynomial.decodeCubic 24 atom0398Coded := by decide +kernel
theorem atom0398Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded) := by
  have h := atom0398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0399 : SparsePolynomial.Poly := [([0,9,19], 1)]
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
def atom0399Coded : CoefficientMerge.Poly := [(235, 1)]
theorem atom0399Coded_decode : atom0399 = SparsePolynomial.decodeCubic 24 atom0399Coded := by decide +kernel
theorem atom0399Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) := by
  have h := atom0399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0400 : SparsePolynomial.Poly := [([0,9,20], 1)]
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
def atom0400Coded : CoefficientMerge.Poly := [(236, 1)]
theorem atom0400Coded_decode : atom0400 = SparsePolynomial.decodeCubic 24 atom0400Coded := by decide +kernel
theorem atom0400Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded) := by
  have h := atom0400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0401 : SparsePolynomial.Poly := [([0,9,21], 1)]
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
def atom0401Coded : CoefficientMerge.Poly := [(237, 1)]
theorem atom0401Coded_decode : atom0401 = SparsePolynomial.decodeCubic 24 atom0401Coded := by decide +kernel
theorem atom0401Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) := by
  have h := atom0401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0402 : SparsePolynomial.Poly := [([0,9,22], 1)]
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
def atom0402Coded : CoefficientMerge.Poly := [(238, 1)]
theorem atom0402Coded_decode : atom0402 = SparsePolynomial.decodeCubic 24 atom0402Coded := by decide +kernel
theorem atom0402Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) := by
  have h := atom0402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0403 : SparsePolynomial.Poly := [([0,9,23], 1)]
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
def atom0403Coded : CoefficientMerge.Poly := [(239, 1)]
theorem atom0403Coded_decode : atom0403 = SparsePolynomial.decodeCubic 24 atom0403Coded := by decide +kernel
theorem atom0403Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded) := by
  have h := atom0403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0404 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145564793865216 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404Coded : CoefficientMerge.Poly := [(250, 1)]
theorem atom0404Coded_decode : atom0404 = SparsePolynomial.decodeCubic 24 atom0404Coded := by decide +kernel
theorem atom0404Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) := by
  have h := atom0404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0405 : SparsePolynomial.Poly := [([0,10,11], 1)]
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
def atom0405Coded : CoefficientMerge.Poly := [(251, 1)]
theorem atom0405Coded_decode : atom0405 = SparsePolynomial.decodeCubic 24 atom0405Coded := by decide +kernel
theorem atom0405Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded) := by
  have h := atom0405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0406 : SparsePolynomial.Poly := [([0,10,12], 1)]
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
def atom0406Coded : CoefficientMerge.Poly := [(252, 1)]
theorem atom0406Coded_decode : atom0406 = SparsePolynomial.decodeCubic 24 atom0406Coded := by decide +kernel
theorem atom0406Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) := by
  have h := atom0406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0407 : SparsePolynomial.Poly := [([0,10,13], 1)]
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
def atom0407Coded : CoefficientMerge.Poly := [(253, 1)]
theorem atom0407Coded_decode : atom0407 = SparsePolynomial.decodeCubic 24 atom0407Coded := by decide +kernel
theorem atom0407Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) := by
  have h := atom0407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0408 : SparsePolynomial.Poly := [([0,10,14], 1)]
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
def atom0408Coded : CoefficientMerge.Poly := [(254, 1)]
theorem atom0408Coded_decode : atom0408 = SparsePolynomial.decodeCubic 24 atom0408Coded := by decide +kernel
theorem atom0408Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded) := by
  have h := atom0408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0409 : SparsePolynomial.Poly := [([0,10,15], 1)]
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
def atom0409Coded : CoefficientMerge.Poly := [(255, 1)]
theorem atom0409Coded_decode : atom0409 = SparsePolynomial.decodeCubic 24 atom0409Coded := by decide +kernel
theorem atom0409Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) := by
  have h := atom0409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0410 : SparsePolynomial.Poly := [([0,10,16], 1)]
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
def atom0410Coded : CoefficientMerge.Poly := [(256, 1)]
theorem atom0410Coded_decode : atom0410 = SparsePolynomial.decodeCubic 24 atom0410Coded := by decide +kernel
theorem atom0410Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded) := by
  have h := atom0410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0411 : SparsePolynomial.Poly := [([0,10,17], 1)]
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
def atom0411Coded : CoefficientMerge.Poly := [(257, 1)]
theorem atom0411Coded_decode : atom0411 = SparsePolynomial.decodeCubic 24 atom0411Coded := by decide +kernel
theorem atom0411Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) := by
  have h := atom0411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0412 : SparsePolynomial.Poly := [([0,10,18], 1)]
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
def atom0412Coded : CoefficientMerge.Poly := [(258, 1)]
theorem atom0412Coded_decode : atom0412 = SparsePolynomial.decodeCubic 24 atom0412Coded := by decide +kernel
theorem atom0412Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) := by
  have h := atom0412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0413 : SparsePolynomial.Poly := [([0,10,19], 1)]
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
def atom0413Coded : CoefficientMerge.Poly := [(259, 1)]
theorem atom0413Coded_decode : atom0413 = SparsePolynomial.decodeCubic 24 atom0413Coded := by decide +kernel
theorem atom0413Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded) := by
  have h := atom0413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0414 : SparsePolynomial.Poly := [([0,10,20], 1)]
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
def atom0414Coded : CoefficientMerge.Poly := [(260, 1)]
theorem atom0414Coded_decode : atom0414 = SparsePolynomial.decodeCubic 24 atom0414Coded := by decide +kernel
theorem atom0414Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) := by
  have h := atom0414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0415 : SparsePolynomial.Poly := [([0,10,21], 1)]
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
def atom0415Coded : CoefficientMerge.Poly := [(261, 1)]
theorem atom0415Coded_decode : atom0415 = SparsePolynomial.decodeCubic 24 atom0415Coded := by decide +kernel
theorem atom0415Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded) := by
  have h := atom0415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0416 : SparsePolynomial.Poly := [([0,10,22], 1)]
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
def atom0416Coded : CoefficientMerge.Poly := [(262, 1)]
theorem atom0416Coded_decode : atom0416 = SparsePolynomial.decodeCubic 24 atom0416Coded := by decide +kernel
theorem atom0416Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) := by
  have h := atom0416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0417 : SparsePolynomial.Poly := [([0,10,23], 1)]
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
def atom0417Coded : CoefficientMerge.Poly := [(263, 1)]
theorem atom0417Coded_decode : atom0417 = SparsePolynomial.decodeCubic 24 atom0417Coded := by decide +kernel
theorem atom0417Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) := by
  have h := atom0417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0418 : SparsePolynomial.Poly := [([0,11,11], 1)]
theorem eval_atom0418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0418 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159353351125056 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418Coded : CoefficientMerge.Poly := [(275, 1)]
theorem atom0418Coded_decode : atom0418 = SparsePolynomial.decodeCubic 24 atom0418Coded := by decide +kernel
theorem atom0418Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded) := by
  have h := atom0418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0419 : SparsePolynomial.Poly := [([0,11,12], 1)]
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
def atom0419Coded : CoefficientMerge.Poly := [(276, 1)]
theorem atom0419Coded_decode : atom0419 = SparsePolynomial.decodeCubic 24 atom0419Coded := by decide +kernel
theorem atom0419Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) := by
  have h := atom0419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0420 : SparsePolynomial.Poly := [([0,11,13], 1)]
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
def atom0420Coded : CoefficientMerge.Poly := [(277, 1)]
theorem atom0420Coded_decode : atom0420 = SparsePolynomial.decodeCubic 24 atom0420Coded := by decide +kernel
theorem atom0420Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded) := by
  have h := atom0420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0421 : SparsePolynomial.Poly := [([0,11,14], 1)]
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
def atom0421Coded : CoefficientMerge.Poly := [(278, 1)]
theorem atom0421Coded_decode : atom0421 = SparsePolynomial.decodeCubic 24 atom0421Coded := by decide +kernel
theorem atom0421Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) := by
  have h := atom0421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0422 : SparsePolynomial.Poly := [([0,11,15], 1)]
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
def atom0422Coded : CoefficientMerge.Poly := [(279, 1)]
theorem atom0422Coded_decode : atom0422 = SparsePolynomial.decodeCubic 24 atom0422Coded := by decide +kernel
theorem atom0422Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) := by
  have h := atom0422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0423 : SparsePolynomial.Poly := [([0,11,16], 1)]
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
def atom0423Coded : CoefficientMerge.Poly := [(280, 1)]
theorem atom0423Coded_decode : atom0423 = SparsePolynomial.decodeCubic 24 atom0423Coded := by decide +kernel
theorem atom0423Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded) := by
  have h := atom0423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0424 : SparsePolynomial.Poly := [([0,11,17], 1)]
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
def atom0424Coded : CoefficientMerge.Poly := [(281, 1)]
theorem atom0424Coded_decode : atom0424 = SparsePolynomial.decodeCubic 24 atom0424Coded := by decide +kernel
theorem atom0424Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) := by
  have h := atom0424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0425 : SparsePolynomial.Poly := [([0,11,18], 1)]
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
def atom0425Coded : CoefficientMerge.Poly := [(282, 1)]
theorem atom0425Coded_decode : atom0425 = SparsePolynomial.decodeCubic 24 atom0425Coded := by decide +kernel
theorem atom0425Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded) := by
  have h := atom0425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0426 : SparsePolynomial.Poly := [([0,11,19], 1)]
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
def atom0426Coded : CoefficientMerge.Poly := [(283, 1)]
theorem atom0426Coded_decode : atom0426 = SparsePolynomial.decodeCubic 24 atom0426Coded := by decide +kernel
theorem atom0426Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) := by
  have h := atom0426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0427 : SparsePolynomial.Poly := [([0,11,20], 1)]
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
def atom0427Coded : CoefficientMerge.Poly := [(284, 1)]
theorem atom0427Coded_decode : atom0427 = SparsePolynomial.decodeCubic 24 atom0427Coded := by decide +kernel
theorem atom0427Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) := by
  have h := atom0427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0428 : SparsePolynomial.Poly := [([0,11,21], 1)]
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
def atom0428Coded : CoefficientMerge.Poly := [(285, 1)]
theorem atom0428Coded_decode : atom0428 = SparsePolynomial.decodeCubic 24 atom0428Coded := by decide +kernel
theorem atom0428Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded) := by
  have h := atom0428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0429 : SparsePolynomial.Poly := [([0,11,22], 1)]
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
def atom0429Coded : CoefficientMerge.Poly := [(286, 1)]
theorem atom0429Coded_decode : atom0429 = SparsePolynomial.decodeCubic 24 atom0429Coded := by decide +kernel
theorem atom0429Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) := by
  have h := atom0429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0430 : SparsePolynomial.Poly := [([0,11,23], 1)]
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
def atom0430Coded : CoefficientMerge.Poly := [(287, 1)]
theorem atom0430Coded_decode : atom0430 = SparsePolynomial.decodeCubic 24 atom0430Coded := by decide +kernel
theorem atom0430Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded) := by
  have h := atom0430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0431 : SparsePolynomial.Poly := [([0,12,12], 1)]
theorem eval_atom0431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0431 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204859561585536 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431Coded : CoefficientMerge.Poly := [(300, 1)]
theorem atom0431Coded_decode : atom0431 = SparsePolynomial.decodeCubic 24 atom0431Coded := by decide +kernel
theorem atom0431Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) := by
  have h := atom0431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0432 : SparsePolynomial.Poly := [([0,12,13], 1)]
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
def atom0432Coded : CoefficientMerge.Poly := [(301, 1)]
theorem atom0432Coded_decode : atom0432 = SparsePolynomial.decodeCubic 24 atom0432Coded := by decide +kernel
theorem atom0432Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) := by
  have h := atom0432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0433 : SparsePolynomial.Poly := [([0,12,14], 1)]
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
def atom0433Coded : CoefficientMerge.Poly := [(302, 1)]
theorem atom0433Coded_decode : atom0433 = SparsePolynomial.decodeCubic 24 atom0433Coded := by decide +kernel
theorem atom0433Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded) := by
  have h := atom0433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0434 : SparsePolynomial.Poly := [([0,12,15], 1)]
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
def atom0434Coded : CoefficientMerge.Poly := [(303, 1)]
theorem atom0434Coded_decode : atom0434 = SparsePolynomial.decodeCubic 24 atom0434Coded := by decide +kernel
theorem atom0434Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) := by
  have h := atom0434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0435 : SparsePolynomial.Poly := [([0,12,16], 1)]
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
def atom0435Coded : CoefficientMerge.Poly := [(304, 1)]
theorem atom0435Coded_decode : atom0435 = SparsePolynomial.decodeCubic 24 atom0435Coded := by decide +kernel
theorem atom0435Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded) := by
  have h := atom0435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0436 : SparsePolynomial.Poly := [([0,12,17], 1)]
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
def atom0436Coded : CoefficientMerge.Poly := [(305, 1)]
theorem atom0436Coded_decode : atom0436 = SparsePolynomial.decodeCubic 24 atom0436Coded := by decide +kernel
theorem atom0436Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) := by
  have h := atom0436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0437 : SparsePolynomial.Poly := [([0,12,18], 1)]
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
def atom0437Coded : CoefficientMerge.Poly := [(306, 1)]
theorem atom0437Coded_decode : atom0437 = SparsePolynomial.decodeCubic 24 atom0437Coded := by decide +kernel
theorem atom0437Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) := by
  have h := atom0437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0438 : SparsePolynomial.Poly := [([0,12,19], 1)]
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
def atom0438Coded : CoefficientMerge.Poly := [(307, 1)]
theorem atom0438Coded_decode : atom0438 = SparsePolynomial.decodeCubic 24 atom0438Coded := by decide +kernel
theorem atom0438Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded) := by
  have h := atom0438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0439 : SparsePolynomial.Poly := [([0,12,20], 1)]
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
def atom0439Coded : CoefficientMerge.Poly := [(308, 1)]
theorem atom0439Coded_decode : atom0439 = SparsePolynomial.decodeCubic 24 atom0439Coded := by decide +kernel
theorem atom0439Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) := by
  have h := atom0439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0440 : SparsePolynomial.Poly := [([0,12,21], 1)]
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
def atom0440Coded : CoefficientMerge.Poly := [(309, 1)]
theorem atom0440Coded_decode : atom0440 = SparsePolynomial.decodeCubic 24 atom0440Coded := by decide +kernel
theorem atom0440Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded) := by
  have h := atom0440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0441 : SparsePolynomial.Poly := [([0,12,22], 1)]
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
def atom0441Coded : CoefficientMerge.Poly := [(310, 1)]
theorem atom0441Coded_decode : atom0441 = SparsePolynomial.decodeCubic 24 atom0441Coded := by decide +kernel
theorem atom0441Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) := by
  have h := atom0441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0442 : SparsePolynomial.Poly := [([0,12,23], 1)]
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
def atom0442Coded : CoefficientMerge.Poly := [(311, 1)]
theorem atom0442Coded_decode : atom0442 = SparsePolynomial.decodeCubic 24 atom0442Coded := by decide +kernel
theorem atom0442Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) := by
  have h := atom0442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0443 : SparsePolynomial.Poly := [([0,13,13], 1)]
theorem eval_atom0443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0443 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197453219040000 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443Coded : CoefficientMerge.Poly := [(325, 1)]
theorem atom0443Coded_decode : atom0443 = SparsePolynomial.decodeCubic 24 atom0443Coded := by decide +kernel
theorem atom0443Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded) := by
  have h := atom0443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0444 : SparsePolynomial.Poly := [([0,13,14], 1)]
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
def atom0444Coded : CoefficientMerge.Poly := [(326, 1)]
theorem atom0444Coded_decode : atom0444 = SparsePolynomial.decodeCubic 24 atom0444Coded := by decide +kernel
theorem atom0444Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) := by
  have h := atom0444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0445 : SparsePolynomial.Poly := [([0,13,15], 1)]
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
def atom0445Coded : CoefficientMerge.Poly := [(327, 1)]
theorem atom0445Coded_decode : atom0445 = SparsePolynomial.decodeCubic 24 atom0445Coded := by decide +kernel
theorem atom0445Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded) := by
  have h := atom0445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0446 : SparsePolynomial.Poly := [([0,13,16], 1)]
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
def atom0446Coded : CoefficientMerge.Poly := [(328, 1)]
theorem atom0446Coded_decode : atom0446 = SparsePolynomial.decodeCubic 24 atom0446Coded := by decide +kernel
theorem atom0446Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) := by
  have h := atom0446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0447 : SparsePolynomial.Poly := [([0,13,17], 1)]
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
def atom0447Coded : CoefficientMerge.Poly := [(329, 1)]
theorem atom0447Coded_decode : atom0447 = SparsePolynomial.decodeCubic 24 atom0447Coded := by decide +kernel
theorem atom0447Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) := by
  have h := atom0447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0448 : SparsePolynomial.Poly := [([0,13,18], 1)]
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
def atom0448Coded : CoefficientMerge.Poly := [(330, 1)]
theorem atom0448Coded_decode : atom0448 = SparsePolynomial.decodeCubic 24 atom0448Coded := by decide +kernel
theorem atom0448Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded) := by
  have h := atom0448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(188, 145973111961600), (189, 91276900915200), (190, 101070199171200), (191, 66423577651200), (200, 130635871027200), (201, 238603162254336), (202, 205050002305500), (203, 206244770071032), (204, 254087646219792), (205, 238680835192800), (206, 216844064236800), (207, 222147409478400), (208, 230406382281600), (209, 236182170470400), (210, 254053174636800), (211, 193981723689600), (212, 155076940972800), (213, 102043327478400), (214, 111957702998400), (215, 77432158742400), (225, 144531443713536), (226, 253532085092352), (227, 229630294124352), (228, 266810264348760), (229, 250127712393768), (230, 227785960653768), (231, 232584325111368), (232, 240338317130568), (233, 245609124535368), (234, 264258199992996), (235, 206247872412252), (236, 170868583296972), (237, 120997827084420), (238, 126521758552140), (239, 96623441813052), (250, 145564793865216), (251, 266333360622912), (252, 281629959463512), (253, 262721401588008), (254, 239619520878408), (255, 243657756366408), (256, 250651619416008), (257, 255162297851208), (258, 276374549456676), (259, 224250703141212), (260, 202038123520332), (261, 157420230578820), (262, 149012007995340), (263, 131646782756412), (275, 159353351125056), (276, 325628128343232), (277, 285505542588816), (278, 253912851994032), (279, 256165050182832), (280, 262143636077232), (281, 265639037357232), (282, 291518936774208), (283, 241024102148016), (284, 231218915577408), (285, 188817502897584), (286, 166489350215040), (287, 159211799569152), (300, 204859561585536), (301, 363727996258176), (302, 314919946272096), (303, 314422158328992), (304, 319130318882592), (305, 321355294821792), (306, 352380815538048), (307, 291890417851296), (308, 294121979826048), (309, 232524785759904), (310, 163964446295040), (311, 152337682202112), (325, 197453219040000), (326, 339075700064640), (327, 310411363872960), (328, 310881610468800), (329, 311581012881600), (330, 340076468793600)]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145973111961600 : Int) atom0369Coded) (CoefficientMerge.scale (91276900915200 : Int) atom0370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101070199171200 : Int) atom0371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66423577651200 : Int) atom0372Coded) (CoefficientMerge.scale (130635871027200 : Int) atom0373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (238603162254336 : Int) atom0374Coded) (CoefficientMerge.scale (205050002305500 : Int) atom0375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206244770071032 : Int) atom0376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254087646219792 : Int) atom0377Coded) (CoefficientMerge.scale (238680835192800 : Int) atom0378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (216844064236800 : Int) atom0379Coded) (CoefficientMerge.scale (222147409478400 : Int) atom0380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230406382281600 : Int) atom0381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236182170470400 : Int) atom0382Coded) (CoefficientMerge.scale (254053174636800 : Int) atom0383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193981723689600 : Int) atom0384Coded) (CoefficientMerge.scale (155076940972800 : Int) atom0385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102043327478400 : Int) atom0386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (111957702998400 : Int) atom0387Coded) (CoefficientMerge.scale (77432158742400 : Int) atom0388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144531443713536 : Int) atom0389Coded) (CoefficientMerge.scale (253532085092352 : Int) atom0390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229630294124352 : Int) atom0391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266810264348760 : Int) atom0392Coded) (CoefficientMerge.scale (250127712393768 : Int) atom0393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227785960653768 : Int) atom0394Coded) (CoefficientMerge.scale (232584325111368 : Int) atom0395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (240338317130568 : Int) atom0396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245609124535368 : Int) atom0397Coded) (CoefficientMerge.scale (264258199992996 : Int) atom0398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (206247872412252 : Int) atom0399Coded) (CoefficientMerge.scale (170868583296972 : Int) atom0400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120997827084420 : Int) atom0401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126521758552140 : Int) atom0402Coded) (CoefficientMerge.scale (96623441813052 : Int) atom0403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145564793865216 : Int) atom0404Coded) (CoefficientMerge.scale (266333360622912 : Int) atom0405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (281629959463512 : Int) atom0406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262721401588008 : Int) atom0407Coded) (CoefficientMerge.scale (239619520878408 : Int) atom0408Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (243657756366408 : Int) atom0409Coded) (CoefficientMerge.scale (250651619416008 : Int) atom0410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (255162297851208 : Int) atom0411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276374549456676 : Int) atom0412Coded) (CoefficientMerge.scale (224250703141212 : Int) atom0413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202038123520332 : Int) atom0414Coded) (CoefficientMerge.scale (157420230578820 : Int) atom0415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149012007995340 : Int) atom0416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131646782756412 : Int) atom0417Coded) (CoefficientMerge.scale (159353351125056 : Int) atom0418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (325628128343232 : Int) atom0419Coded) (CoefficientMerge.scale (285505542588816 : Int) atom0420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (253912851994032 : Int) atom0421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256165050182832 : Int) atom0422Coded) (CoefficientMerge.scale (262143636077232 : Int) atom0423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (265639037357232 : Int) atom0424Coded) (CoefficientMerge.scale (291518936774208 : Int) atom0425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241024102148016 : Int) atom0426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231218915577408 : Int) atom0427Coded) (CoefficientMerge.scale (188817502897584 : Int) atom0428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166489350215040 : Int) atom0429Coded) (CoefficientMerge.scale (159211799569152 : Int) atom0430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204859561585536 : Int) atom0431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363727996258176 : Int) atom0432Coded) (CoefficientMerge.scale (314919946272096 : Int) atom0433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (314422158328992 : Int) atom0434Coded) (CoefficientMerge.scale (319130318882592 : Int) atom0435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (321355294821792 : Int) atom0436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352380815538048 : Int) atom0437Coded) (CoefficientMerge.scale (291890417851296 : Int) atom0438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (294121979826048 : Int) atom0439Coded) (CoefficientMerge.scale (232524785759904 : Int) atom0440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163964446295040 : Int) atom0441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152337682202112 : Int) atom0442Coded) (CoefficientMerge.scale (197453219040000 : Int) atom0443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (339075700064640 : Int) atom0444Coded) (CoefficientMerge.scale (310411363872960 : Int) atom0445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (310881610468800 : Int) atom0446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311581012881600 : Int) atom0447Coded) (CoefficientMerge.scale (340076468793600 : Int) atom0448Coded)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0369Coded_nonneg g hg hA hB) (atom0370Coded_nonneg g hg hA hB)) (add_nonneg (atom0371Coded_nonneg g hg hA hB) (add_nonneg (atom0372Coded_nonneg g hg hA hB) (atom0373Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0374Coded_nonneg g hg hA hB) (atom0375Coded_nonneg g hg hA hB)) (add_nonneg (atom0376Coded_nonneg g hg hA hB) (add_nonneg (atom0377Coded_nonneg g hg hA hB) (atom0378Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0379Coded_nonneg g hg hA hB) (atom0380Coded_nonneg g hg hA hB)) (add_nonneg (atom0381Coded_nonneg g hg hA hB) (add_nonneg (atom0382Coded_nonneg g hg hA hB) (atom0383Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0384Coded_nonneg g hg hA hB) (atom0385Coded_nonneg g hg hA hB)) (add_nonneg (atom0386Coded_nonneg g hg hA hB) (add_nonneg (atom0387Coded_nonneg g hg hA hB) (atom0388Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0389Coded_nonneg g hg hA hB) (atom0390Coded_nonneg g hg hA hB)) (add_nonneg (atom0391Coded_nonneg g hg hA hB) (add_nonneg (atom0392Coded_nonneg g hg hA hB) (atom0393Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0394Coded_nonneg g hg hA hB) (atom0395Coded_nonneg g hg hA hB)) (add_nonneg (atom0396Coded_nonneg g hg hA hB) (add_nonneg (atom0397Coded_nonneg g hg hA hB) (atom0398Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0399Coded_nonneg g hg hA hB) (atom0400Coded_nonneg g hg hA hB)) (add_nonneg (atom0401Coded_nonneg g hg hA hB) (add_nonneg (atom0402Coded_nonneg g hg hA hB) (atom0403Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0404Coded_nonneg g hg hA hB) (atom0405Coded_nonneg g hg hA hB)) (add_nonneg (atom0406Coded_nonneg g hg hA hB) (add_nonneg (atom0407Coded_nonneg g hg hA hB) (atom0408Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0409Coded_nonneg g hg hA hB) (atom0410Coded_nonneg g hg hA hB)) (add_nonneg (atom0411Coded_nonneg g hg hA hB) (add_nonneg (atom0412Coded_nonneg g hg hA hB) (atom0413Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0414Coded_nonneg g hg hA hB) (atom0415Coded_nonneg g hg hA hB)) (add_nonneg (atom0416Coded_nonneg g hg hA hB) (add_nonneg (atom0417Coded_nonneg g hg hA hB) (atom0418Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0419Coded_nonneg g hg hA hB) (atom0420Coded_nonneg g hg hA hB)) (add_nonneg (atom0421Coded_nonneg g hg hA hB) (add_nonneg (atom0422Coded_nonneg g hg hA hB) (atom0423Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0424Coded_nonneg g hg hA hB) (atom0425Coded_nonneg g hg hA hB)) (add_nonneg (atom0426Coded_nonneg g hg hA hB) (add_nonneg (atom0427Coded_nonneg g hg hA hB) (atom0428Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0429Coded_nonneg g hg hA hB) (atom0430Coded_nonneg g hg hA hB)) (add_nonneg (atom0431Coded_nonneg g hg hA hB) (add_nonneg (atom0432Coded_nonneg g hg hA hB) (atom0433Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0434Coded_nonneg g hg hA hB) (atom0435Coded_nonneg g hg hA hB)) (add_nonneg (atom0436Coded_nonneg g hg hA hB) (add_nonneg (atom0437Coded_nonneg g hg hA hB) (atom0438Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0439Coded_nonneg g hg hA hB) (atom0440Coded_nonneg g hg hA hB)) (add_nonneg (atom0441Coded_nonneg g hg hA hB) (add_nonneg (atom0442Coded_nonneg g hg hA hB) (atom0443Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0444Coded_nonneg g hg hA hB) (atom0445Coded_nonneg g hg hA hB)) (add_nonneg (atom0446Coded_nonneg g hg hA hB) (add_nonneg (atom0447Coded_nonneg g hg hA hB) (atom0448Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
