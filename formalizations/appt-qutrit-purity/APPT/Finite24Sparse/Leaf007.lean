import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0369 : SparsePolynomial.Poly := [([0,7,20], 1)]
theorem eval_atom0369 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0369 = ((g 0) * (g 7) * (g 20)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0369_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145973111961600 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370 : SparsePolynomial.Poly := [([0,7,21], 1)]
theorem eval_atom0370 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0370 = ((g 0) * (g 7) * (g 21)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0370_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91276900915200 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371 : SparsePolynomial.Poly := [([0,7,22], 1)]
theorem eval_atom0371 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0371 = ((g 0) * (g 7) * (g 22)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0371_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101070199171200 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372 : SparsePolynomial.Poly := [([0,7,23], 1)]
theorem eval_atom0372 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0372 = ((g 0) * (g 7) * (g 23)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0372_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (66423577651200 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0373 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130635871027200 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374 : SparsePolynomial.Poly := [([0,8,9], 1)]
theorem eval_atom0374 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0374 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0374_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238603162254336 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375 : SparsePolynomial.Poly := [([0,8,10], 1)]
theorem eval_atom0375 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0375 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0375_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205050002305500 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376 : SparsePolynomial.Poly := [([0,8,11], 1)]
theorem eval_atom0376 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0376 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0376_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (206244770071032 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377 : SparsePolynomial.Poly := [([0,8,12], 1)]
theorem eval_atom0377 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0377 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0377_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254087646219792 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378 : SparsePolynomial.Poly := [([0,8,13], 1)]
theorem eval_atom0378 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0378 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0378_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238680835192800 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379 : SparsePolynomial.Poly := [([0,8,14], 1)]
theorem eval_atom0379 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0379 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0379_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (216844064236800 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380 : SparsePolynomial.Poly := [([0,8,15], 1)]
theorem eval_atom0380 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0380 = ((g 0) * (g 8) * (g 15)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0380_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (222147409478400 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381 : SparsePolynomial.Poly := [([0,8,16], 1)]
theorem eval_atom0381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0381 = ((g 0) * (g 8) * (g 16)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230406382281600 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382 : SparsePolynomial.Poly := [([0,8,17], 1)]
theorem eval_atom0382 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0382 = ((g 0) * (g 8) * (g 17)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0382_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (236182170470400 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383 : SparsePolynomial.Poly := [([0,8,18], 1)]
theorem eval_atom0383 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0383 = ((g 0) * (g 8) * (g 18)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0383_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254053174636800 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384 : SparsePolynomial.Poly := [([0,8,19], 1)]
theorem eval_atom0384 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0384 = ((g 0) * (g 8) * (g 19)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0384_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193981723689600 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385 : SparsePolynomial.Poly := [([0,8,20], 1)]
theorem eval_atom0385 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0385 = ((g 0) * (g 8) * (g 20)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0385_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (155076940972800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386 : SparsePolynomial.Poly := [([0,8,21], 1)]
theorem eval_atom0386 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0386 = ((g 0) * (g 8) * (g 21)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0386_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102043327478400 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387 : SparsePolynomial.Poly := [([0,8,22], 1)]
theorem eval_atom0387 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0387 = ((g 0) * (g 8) * (g 22)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0387_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (111957702998400 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388 : SparsePolynomial.Poly := [([0,8,23], 1)]
theorem eval_atom0388 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0388 = ((g 0) * (g 8) * (g 23)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0388_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77432158742400 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0389 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144531443713536 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390 : SparsePolynomial.Poly := [([0,9,10], 1)]
theorem eval_atom0390 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0390 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0390_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (253532085092352 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391 : SparsePolynomial.Poly := [([0,9,11], 1)]
theorem eval_atom0391 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0391 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0391_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229630294124352 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392 : SparsePolynomial.Poly := [([0,9,12], 1)]
theorem eval_atom0392 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0392 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0392_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (266810264348760 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393 : SparsePolynomial.Poly := [([0,9,13], 1)]
theorem eval_atom0393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0393 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (250127712393768 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394 : SparsePolynomial.Poly := [([0,9,14], 1)]
theorem eval_atom0394 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0394 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0394_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (227785960653768 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395 : SparsePolynomial.Poly := [([0,9,15], 1)]
theorem eval_atom0395 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0395 = ((g 0) * (g 9) * (g 15)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0395_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (232584325111368 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396 : SparsePolynomial.Poly := [([0,9,16], 1)]
theorem eval_atom0396 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0396 = ((g 0) * (g 9) * (g 16)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0396_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (240338317130568 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397 : SparsePolynomial.Poly := [([0,9,17], 1)]
theorem eval_atom0397 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0397 = ((g 0) * (g 9) * (g 17)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0397_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (245609124535368 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398 : SparsePolynomial.Poly := [([0,9,18], 1)]
theorem eval_atom0398 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0398 = ((g 0) * (g 9) * (g 18)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0398_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264258199992996 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399 : SparsePolynomial.Poly := [([0,9,19], 1)]
theorem eval_atom0399 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0399 = ((g 0) * (g 9) * (g 19)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0399_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (206247872412252 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400 : SparsePolynomial.Poly := [([0,9,20], 1)]
theorem eval_atom0400 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0400 = ((g 0) * (g 9) * (g 20)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0400_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170868583296972 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401 : SparsePolynomial.Poly := [([0,9,21], 1)]
theorem eval_atom0401 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0401 = ((g 0) * (g 9) * (g 21)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0401_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120997827084420 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402 : SparsePolynomial.Poly := [([0,9,22], 1)]
theorem eval_atom0402 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0402 = ((g 0) * (g 9) * (g 22)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0402_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126521758552140 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403 : SparsePolynomial.Poly := [([0,9,23], 1)]
theorem eval_atom0403 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0403 = ((g 0) * (g 9) * (g 23)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0403_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96623441813052 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0404 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145564793865216 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405 : SparsePolynomial.Poly := [([0,10,11], 1)]
theorem eval_atom0405 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0405 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0405_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (266333360622912 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406 : SparsePolynomial.Poly := [([0,10,12], 1)]
theorem eval_atom0406 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0406 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0406_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (281629959463512 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407 : SparsePolynomial.Poly := [([0,10,13], 1)]
theorem eval_atom0407 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0407 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0407_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (262721401588008 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408 : SparsePolynomial.Poly := [([0,10,14], 1)]
theorem eval_atom0408 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0408 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0408_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (239619520878408 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409 : SparsePolynomial.Poly := [([0,10,15], 1)]
theorem eval_atom0409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0409 = ((g 0) * (g 10) * (g 15)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (243657756366408 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410 : SparsePolynomial.Poly := [([0,10,16], 1)]
theorem eval_atom0410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0410 = ((g 0) * (g 10) * (g 16)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (250651619416008 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411 : SparsePolynomial.Poly := [([0,10,17], 1)]
theorem eval_atom0411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0411 = ((g 0) * (g 10) * (g 17)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (255162297851208 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412 : SparsePolynomial.Poly := [([0,10,18], 1)]
theorem eval_atom0412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0412 = ((g 0) * (g 10) * (g 18)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (276374549456676 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413 : SparsePolynomial.Poly := [([0,10,19], 1)]
theorem eval_atom0413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0413 = ((g 0) * (g 10) * (g 19)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (224250703141212 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414 : SparsePolynomial.Poly := [([0,10,20], 1)]
theorem eval_atom0414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0414 = ((g 0) * (g 10) * (g 20)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (202038123520332 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415 : SparsePolynomial.Poly := [([0,10,21], 1)]
theorem eval_atom0415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0415 = ((g 0) * (g 10) * (g 21)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157420230578820 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416 : SparsePolynomial.Poly := [([0,10,22], 1)]
theorem eval_atom0416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0416 = ((g 0) * (g 10) * (g 22)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149012007995340 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417 : SparsePolynomial.Poly := [([0,10,23], 1)]
theorem eval_atom0417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0417 = ((g 0) * (g 10) * (g 23)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (131646782756412 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418 : SparsePolynomial.Poly := [([0,11,11], 1)]
theorem eval_atom0418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0418 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159353351125056 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419 : SparsePolynomial.Poly := [([0,11,12], 1)]
theorem eval_atom0419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0419 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (325628128343232 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420 : SparsePolynomial.Poly := [([0,11,13], 1)]
theorem eval_atom0420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0420 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (285505542588816 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421 : SparsePolynomial.Poly := [([0,11,14], 1)]
theorem eval_atom0421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0421 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (253912851994032 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422 : SparsePolynomial.Poly := [([0,11,15], 1)]
theorem eval_atom0422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0422 = ((g 0) * (g 11) * (g 15)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256165050182832 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423 : SparsePolynomial.Poly := [([0,11,16], 1)]
theorem eval_atom0423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0423 = ((g 0) * (g 11) * (g 16)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (262143636077232 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424 : SparsePolynomial.Poly := [([0,11,17], 1)]
theorem eval_atom0424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0424 = ((g 0) * (g 11) * (g 17)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (265639037357232 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425 : SparsePolynomial.Poly := [([0,11,18], 1)]
theorem eval_atom0425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0425 = ((g 0) * (g 11) * (g 18)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (291518936774208 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426 : SparsePolynomial.Poly := [([0,11,19], 1)]
theorem eval_atom0426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0426 = ((g 0) * (g 11) * (g 19)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241024102148016 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427 : SparsePolynomial.Poly := [([0,11,20], 1)]
theorem eval_atom0427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0427 = ((g 0) * (g 11) * (g 20)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (231218915577408 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428 : SparsePolynomial.Poly := [([0,11,21], 1)]
theorem eval_atom0428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0428 = ((g 0) * (g 11) * (g 21)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188817502897584 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429 : SparsePolynomial.Poly := [([0,11,22], 1)]
theorem eval_atom0429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0429 = ((g 0) * (g 11) * (g 22)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166489350215040 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430 : SparsePolynomial.Poly := [([0,11,23], 1)]
theorem eval_atom0430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0430 = ((g 0) * (g 11) * (g 23)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159211799569152 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431 : SparsePolynomial.Poly := [([0,12,12], 1)]
theorem eval_atom0431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0431 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (204859561585536 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432 : SparsePolynomial.Poly := [([0,12,13], 1)]
theorem eval_atom0432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0432 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (363727996258176 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433 : SparsePolynomial.Poly := [([0,12,14], 1)]
theorem eval_atom0433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0433 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (314919946272096 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434 : SparsePolynomial.Poly := [([0,12,15], 1)]
theorem eval_atom0434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0434 = ((g 0) * (g 12) * (g 15)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (314422158328992 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435 : SparsePolynomial.Poly := [([0,12,16], 1)]
theorem eval_atom0435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0435 = ((g 0) * (g 12) * (g 16)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (319130318882592 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436 : SparsePolynomial.Poly := [([0,12,17], 1)]
theorem eval_atom0436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0436 = ((g 0) * (g 12) * (g 17)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (321355294821792 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437 : SparsePolynomial.Poly := [([0,12,18], 1)]
theorem eval_atom0437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0437 = ((g 0) * (g 12) * (g 18)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (352380815538048 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438 : SparsePolynomial.Poly := [([0,12,19], 1)]
theorem eval_atom0438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0438 = ((g 0) * (g 12) * (g 19)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (291890417851296 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439 : SparsePolynomial.Poly := [([0,12,20], 1)]
theorem eval_atom0439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0439 = ((g 0) * (g 12) * (g 20)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (294121979826048 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440 : SparsePolynomial.Poly := [([0,12,21], 1)]
theorem eval_atom0440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0440 = ((g 0) * (g 12) * (g 21)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (232524785759904 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441 : SparsePolynomial.Poly := [([0,12,22], 1)]
theorem eval_atom0441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0441 = ((g 0) * (g 12) * (g 22)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163964446295040 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442 : SparsePolynomial.Poly := [([0,12,23], 1)]
theorem eval_atom0442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0442 = ((g 0) * (g 12) * (g 23)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152337682202112 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443 : SparsePolynomial.Poly := [([0,13,13], 1)]
theorem eval_atom0443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0443 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197453219040000 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444 : SparsePolynomial.Poly := [([0,13,14], 1)]
theorem eval_atom0444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0444 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (339075700064640 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445 : SparsePolynomial.Poly := [([0,13,15], 1)]
theorem eval_atom0445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0445 = ((g 0) * (g 13) * (g 15)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (310411363872960 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446 : SparsePolynomial.Poly := [([0,13,16], 1)]
theorem eval_atom0446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0446 = ((g 0) * (g 13) * (g 16)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (310881610468800 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447 : SparsePolynomial.Poly := [([0,13,17], 1)]
theorem eval_atom0447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0447 = ((g 0) * (g 13) * (g 17)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (311581012881600 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448 : SparsePolynomial.Poly := [([0,13,18], 1)]
theorem eval_atom0448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0448 = ((g 0) * (g 13) * (g 18)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (340076468793600 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block007 : SparsePolynomial.Poly := [([0,7,20], 145973111961600), ([0,7,21], 91276900915200), ([0,7,22], 101070199171200), ([0,7,23], 66423577651200), ([0,8,8], 130635871027200), ([0,8,9], 238603162254336), ([0,8,10], 205050002305500), ([0,8,11], 206244770071032), ([0,8,12], 254087646219792), ([0,8,13], 238680835192800), ([0,8,14], 216844064236800), ([0,8,15], 222147409478400), ([0,8,16], 230406382281600), ([0,8,17], 236182170470400), ([0,8,18], 254053174636800), ([0,8,19], 193981723689600), ([0,8,20], 155076940972800), ([0,8,21], 102043327478400), ([0,8,22], 111957702998400), ([0,8,23], 77432158742400), ([0,9,9], 144531443713536), ([0,9,10], 253532085092352), ([0,9,11], 229630294124352), ([0,9,12], 266810264348760), ([0,9,13], 250127712393768), ([0,9,14], 227785960653768), ([0,9,15], 232584325111368), ([0,9,16], 240338317130568), ([0,9,17], 245609124535368), ([0,9,18], 264258199992996), ([0,9,19], 206247872412252), ([0,9,20], 170868583296972), ([0,9,21], 120997827084420), ([0,9,22], 126521758552140), ([0,9,23], 96623441813052), ([0,10,10], 145564793865216), ([0,10,11], 266333360622912), ([0,10,12], 281629959463512), ([0,10,13], 262721401588008), ([0,10,14], 239619520878408), ([0,10,15], 243657756366408), ([0,10,16], 250651619416008), ([0,10,17], 255162297851208), ([0,10,18], 276374549456676), ([0,10,19], 224250703141212), ([0,10,20], 202038123520332), ([0,10,21], 157420230578820), ([0,10,22], 149012007995340), ([0,10,23], 131646782756412), ([0,11,11], 159353351125056), ([0,11,12], 325628128343232), ([0,11,13], 285505542588816), ([0,11,14], 253912851994032), ([0,11,15], 256165050182832), ([0,11,16], 262143636077232), ([0,11,17], 265639037357232), ([0,11,18], 291518936774208), ([0,11,19], 241024102148016), ([0,11,20], 231218915577408), ([0,11,21], 188817502897584), ([0,11,22], 166489350215040), ([0,11,23], 159211799569152), ([0,12,12], 204859561585536), ([0,12,13], 363727996258176), ([0,12,14], 314919946272096), ([0,12,15], 314422158328992), ([0,12,16], 319130318882592), ([0,12,17], 321355294821792), ([0,12,18], 352380815538048), ([0,12,19], 291890417851296), ([0,12,20], 294121979826048), ([0,12,21], 232524785759904), ([0,12,22], 163964446295040), ([0,12,23], 152337682202112), ([0,13,13], 197453219040000), ([0,13,14], 339075700064640), ([0,13,15], 310411363872960), ([0,13,16], 310881610468800), ([0,13,17], 311581012881600), ([0,13,18], 340076468793600)]
theorem block007_data : block007 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (145973111961600 : Int) atom0369) (SparsePolynomial.scale (91276900915200 : Int) atom0370)) (SparsePolynomial.merge (SparsePolynomial.scale (101070199171200 : Int) atom0371) (SparsePolynomial.merge (SparsePolynomial.scale (66423577651200 : Int) atom0372) (SparsePolynomial.scale (130635871027200 : Int) atom0373)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (238603162254336 : Int) atom0374) (SparsePolynomial.scale (205050002305500 : Int) atom0375)) (SparsePolynomial.merge (SparsePolynomial.scale (206244770071032 : Int) atom0376) (SparsePolynomial.merge (SparsePolynomial.scale (254087646219792 : Int) atom0377) (SparsePolynomial.scale (238680835192800 : Int) atom0378))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (216844064236800 : Int) atom0379) (SparsePolynomial.scale (222147409478400 : Int) atom0380)) (SparsePolynomial.merge (SparsePolynomial.scale (230406382281600 : Int) atom0381) (SparsePolynomial.merge (SparsePolynomial.scale (236182170470400 : Int) atom0382) (SparsePolynomial.scale (254053174636800 : Int) atom0383)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (193981723689600 : Int) atom0384) (SparsePolynomial.scale (155076940972800 : Int) atom0385)) (SparsePolynomial.merge (SparsePolynomial.scale (102043327478400 : Int) atom0386) (SparsePolynomial.merge (SparsePolynomial.scale (111957702998400 : Int) atom0387) (SparsePolynomial.scale (77432158742400 : Int) atom0388)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (144531443713536 : Int) atom0389) (SparsePolynomial.scale (253532085092352 : Int) atom0390)) (SparsePolynomial.merge (SparsePolynomial.scale (229630294124352 : Int) atom0391) (SparsePolynomial.merge (SparsePolynomial.scale (266810264348760 : Int) atom0392) (SparsePolynomial.scale (250127712393768 : Int) atom0393)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (227785960653768 : Int) atom0394) (SparsePolynomial.scale (232584325111368 : Int) atom0395)) (SparsePolynomial.merge (SparsePolynomial.scale (240338317130568 : Int) atom0396) (SparsePolynomial.merge (SparsePolynomial.scale (245609124535368 : Int) atom0397) (SparsePolynomial.scale (264258199992996 : Int) atom0398))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (206247872412252 : Int) atom0399) (SparsePolynomial.scale (170868583296972 : Int) atom0400)) (SparsePolynomial.merge (SparsePolynomial.scale (120997827084420 : Int) atom0401) (SparsePolynomial.merge (SparsePolynomial.scale (126521758552140 : Int) atom0402) (SparsePolynomial.scale (96623441813052 : Int) atom0403)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (145564793865216 : Int) atom0404) (SparsePolynomial.scale (266333360622912 : Int) atom0405)) (SparsePolynomial.merge (SparsePolynomial.scale (281629959463512 : Int) atom0406) (SparsePolynomial.merge (SparsePolynomial.scale (262721401588008 : Int) atom0407) (SparsePolynomial.scale (239619520878408 : Int) atom0408))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (243657756366408 : Int) atom0409) (SparsePolynomial.scale (250651619416008 : Int) atom0410)) (SparsePolynomial.merge (SparsePolynomial.scale (255162297851208 : Int) atom0411) (SparsePolynomial.merge (SparsePolynomial.scale (276374549456676 : Int) atom0412) (SparsePolynomial.scale (224250703141212 : Int) atom0413)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (202038123520332 : Int) atom0414) (SparsePolynomial.scale (157420230578820 : Int) atom0415)) (SparsePolynomial.merge (SparsePolynomial.scale (149012007995340 : Int) atom0416) (SparsePolynomial.merge (SparsePolynomial.scale (131646782756412 : Int) atom0417) (SparsePolynomial.scale (159353351125056 : Int) atom0418))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (325628128343232 : Int) atom0419) (SparsePolynomial.scale (285505542588816 : Int) atom0420)) (SparsePolynomial.merge (SparsePolynomial.scale (253912851994032 : Int) atom0421) (SparsePolynomial.merge (SparsePolynomial.scale (256165050182832 : Int) atom0422) (SparsePolynomial.scale (262143636077232 : Int) atom0423)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (265639037357232 : Int) atom0424) (SparsePolynomial.scale (291518936774208 : Int) atom0425)) (SparsePolynomial.merge (SparsePolynomial.scale (241024102148016 : Int) atom0426) (SparsePolynomial.merge (SparsePolynomial.scale (231218915577408 : Int) atom0427) (SparsePolynomial.scale (188817502897584 : Int) atom0428)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (166489350215040 : Int) atom0429) (SparsePolynomial.scale (159211799569152 : Int) atom0430)) (SparsePolynomial.merge (SparsePolynomial.scale (204859561585536 : Int) atom0431) (SparsePolynomial.merge (SparsePolynomial.scale (363727996258176 : Int) atom0432) (SparsePolynomial.scale (314919946272096 : Int) atom0433)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (314422158328992 : Int) atom0434) (SparsePolynomial.scale (319130318882592 : Int) atom0435)) (SparsePolynomial.merge (SparsePolynomial.scale (321355294821792 : Int) atom0436) (SparsePolynomial.merge (SparsePolynomial.scale (352380815538048 : Int) atom0437) (SparsePolynomial.scale (291890417851296 : Int) atom0438))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (294121979826048 : Int) atom0439) (SparsePolynomial.scale (232524785759904 : Int) atom0440)) (SparsePolynomial.merge (SparsePolynomial.scale (163964446295040 : Int) atom0441) (SparsePolynomial.merge (SparsePolynomial.scale (152337682202112 : Int) atom0442) (SparsePolynomial.scale (197453219040000 : Int) atom0443)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (339075700064640 : Int) atom0444) (SparsePolynomial.scale (310411363872960 : Int) atom0445)) (SparsePolynomial.merge (SparsePolynomial.scale (310881610468800 : Int) atom0446) (SparsePolynomial.merge (SparsePolynomial.scale (311581012881600 : Int) atom0447) (SparsePolynomial.scale (340076468793600 : Int) atom0448)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block007 := by
  rw [block007_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0369_nonneg g hg hA hB) (atom0370_nonneg g hg hA hB)) (add_nonneg (atom0371_nonneg g hg hA hB) (add_nonneg (atom0372_nonneg g hg hA hB) (atom0373_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0374_nonneg g hg hA hB) (atom0375_nonneg g hg hA hB)) (add_nonneg (atom0376_nonneg g hg hA hB) (add_nonneg (atom0377_nonneg g hg hA hB) (atom0378_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0379_nonneg g hg hA hB) (atom0380_nonneg g hg hA hB)) (add_nonneg (atom0381_nonneg g hg hA hB) (add_nonneg (atom0382_nonneg g hg hA hB) (atom0383_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0384_nonneg g hg hA hB) (atom0385_nonneg g hg hA hB)) (add_nonneg (atom0386_nonneg g hg hA hB) (add_nonneg (atom0387_nonneg g hg hA hB) (atom0388_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0389_nonneg g hg hA hB) (atom0390_nonneg g hg hA hB)) (add_nonneg (atom0391_nonneg g hg hA hB) (add_nonneg (atom0392_nonneg g hg hA hB) (atom0393_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0394_nonneg g hg hA hB) (atom0395_nonneg g hg hA hB)) (add_nonneg (atom0396_nonneg g hg hA hB) (add_nonneg (atom0397_nonneg g hg hA hB) (atom0398_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0399_nonneg g hg hA hB) (atom0400_nonneg g hg hA hB)) (add_nonneg (atom0401_nonneg g hg hA hB) (add_nonneg (atom0402_nonneg g hg hA hB) (atom0403_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0404_nonneg g hg hA hB) (atom0405_nonneg g hg hA hB)) (add_nonneg (atom0406_nonneg g hg hA hB) (add_nonneg (atom0407_nonneg g hg hA hB) (atom0408_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0409_nonneg g hg hA hB) (atom0410_nonneg g hg hA hB)) (add_nonneg (atom0411_nonneg g hg hA hB) (add_nonneg (atom0412_nonneg g hg hA hB) (atom0413_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0414_nonneg g hg hA hB) (atom0415_nonneg g hg hA hB)) (add_nonneg (atom0416_nonneg g hg hA hB) (add_nonneg (atom0417_nonneg g hg hA hB) (atom0418_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0419_nonneg g hg hA hB) (atom0420_nonneg g hg hA hB)) (add_nonneg (atom0421_nonneg g hg hA hB) (add_nonneg (atom0422_nonneg g hg hA hB) (atom0423_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0424_nonneg g hg hA hB) (atom0425_nonneg g hg hA hB)) (add_nonneg (atom0426_nonneg g hg hA hB) (add_nonneg (atom0427_nonneg g hg hA hB) (atom0428_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0429_nonneg g hg hA hB) (atom0430_nonneg g hg hA hB)) (add_nonneg (atom0431_nonneg g hg hA hB) (add_nonneg (atom0432_nonneg g hg hA hB) (atom0433_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0434_nonneg g hg hA hB) (atom0435_nonneg g hg hA hB)) (add_nonneg (atom0436_nonneg g hg hA hB) (add_nonneg (atom0437_nonneg g hg hA hB) (atom0438_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0439_nonneg g hg hA hB) (atom0440_nonneg g hg hA hB)) (add_nonneg (atom0441_nonneg g hg hA hB) (add_nonneg (atom0442_nonneg g hg hA hB) (atom0443_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0444_nonneg g hg hA hB) (atom0445_nonneg g hg hA hB)) (add_nonneg (atom0446_nonneg g hg hA hB) (add_nonneg (atom0447_nonneg g hg hA hB) (atom0448_nonneg g hg hA hB))))))))

end APPT.Finite24
