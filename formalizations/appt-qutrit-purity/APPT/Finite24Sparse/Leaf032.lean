import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2369 : SparsePolynomial.Poly := [([13,16,21], 1)]
theorem eval_atom2369 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2369 = ((g 13) * (g 16) * (g 21)) := by
  norm_num [atom2369, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2369_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (268132862289600 : Int) atom2369) := by
  rw [SparsePolynomial.eval_scale, eval_atom2369]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2370 : SparsePolynomial.Poly := [([13,16,22], 1)]
theorem eval_atom2370 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2370 = ((g 13) * (g 16) * (g 22)) := by
  norm_num [atom2370, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2370_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (255013789363200 : Int) atom2370) := by
  rw [SparsePolynomial.eval_scale, eval_atom2370]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2371 : SparsePolynomial.Poly := [([13,16,23], 1)]
theorem eval_atom2371 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2371 = ((g 13) * (g 16) * (g 23)) := by
  norm_num [atom2371, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2371_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (456770220228000 : Int) atom2371) := by
  rw [SparsePolynomial.eval_scale, eval_atom2371]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2372 : SparsePolynomial.Poly := [([13,17,17], 1)]
theorem eval_atom2372 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2372 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom2372, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2372_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41470439472000 : Int) atom2372) := by
  rw [SparsePolynomial.eval_scale, eval_atom2372]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2373 : SparsePolynomial.Poly := [([13,17,18], 1)]
theorem eval_atom2373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2373 = ((g 13) * (g 17) * (g 18)) := by
  norm_num [atom2373, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130081695004800 : Int) atom2373) := by
  rw [SparsePolynomial.eval_scale, eval_atom2373]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2374 : SparsePolynomial.Poly := [([13,17,19], 1)]
theorem eval_atom2374 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2374 = ((g 13) * (g 17) * (g 19)) := by
  norm_num [atom2374, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2374_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144679235500800 : Int) atom2374) := by
  rw [SparsePolynomial.eval_scale, eval_atom2374]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2375 : SparsePolynomial.Poly := [([13,17,20], 1)]
theorem eval_atom2375 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2375 = ((g 13) * (g 17) * (g 20)) := by
  norm_num [atom2375, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2375_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (412121123568000 : Int) atom2375) := by
  rw [SparsePolynomial.eval_scale, eval_atom2375]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2376 : SparsePolynomial.Poly := [([13,17,21], 1)]
theorem eval_atom2376 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2376 = ((g 13) * (g 17) * (g 21)) := by
  norm_num [atom2376, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2376_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (420077150539200 : Int) atom2376) := by
  rw [SparsePolynomial.eval_scale, eval_atom2376]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2377 : SparsePolynomial.Poly := [([13,17,22], 1)]
theorem eval_atom2377 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2377 = ((g 13) * (g 17) * (g 22)) := by
  norm_num [atom2377, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2377_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (432690996326400 : Int) atom2377) := by
  rw [SparsePolynomial.eval_scale, eval_atom2377]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2378 : SparsePolynomial.Poly := [([13,17,23], 1)]
theorem eval_atom2378 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2378 = ((g 13) * (g 17) * (g 23)) := by
  norm_num [atom2378, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2378_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (655019877204000 : Int) atom2378) := by
  rw [SparsePolynomial.eval_scale, eval_atom2378]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2379 : SparsePolynomial.Poly := [([13,18,18], 1)]
theorem eval_atom2379 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2379 = ((g 13) * (g 18) * (g 18)) := by
  norm_num [atom2379, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2379_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (122580671875200 : Int) atom2379) := by
  rw [SparsePolynomial.eval_scale, eval_atom2379]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2380 : SparsePolynomial.Poly := [([13,18,19], 1)]
theorem eval_atom2380 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2380 = ((g 13) * (g 18) * (g 19)) := by
  norm_num [atom2380, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2380_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (282393592588800 : Int) atom2380) := by
  rw [SparsePolynomial.eval_scale, eval_atom2380]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2381 : SparsePolynomial.Poly := [([13,18,20], 1)]
theorem eval_atom2381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2381 = ((g 13) * (g 18) * (g 20)) := by
  norm_num [atom2381, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (586889813664000 : Int) atom2381) := by
  rw [SparsePolynomial.eval_scale, eval_atom2381]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2382 : SparsePolynomial.Poly := [([13,18,21], 1)]
theorem eval_atom2382 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2382 = ((g 13) * (g 18) * (g 21)) := by
  norm_num [atom2382, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2382_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (616912250169600 : Int) atom2382) := by
  rw [SparsePolynomial.eval_scale, eval_atom2382]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2383 : SparsePolynomial.Poly := [([13,18,22], 1)]
theorem eval_atom2383 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2383 = ((g 13) * (g 18) * (g 22)) := by
  norm_num [atom2383, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2383_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (497465235388800 : Int) atom2383) := by
  rw [SparsePolynomial.eval_scale, eval_atom2383]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2384 : SparsePolynomial.Poly := [([13,18,23], 1)]
theorem eval_atom2384 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2384 = ((g 13) * (g 18) * (g 23)) := by
  norm_num [atom2384, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2384_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (765835096118400 : Int) atom2384) := by
  rw [SparsePolynomial.eval_scale, eval_atom2384]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2385 : SparsePolynomial.Poly := [([13,19,19], 1)]
theorem eval_atom2385 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2385 = ((g 13) * (g 19) * (g 19)) := by
  norm_num [atom2385, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2385_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (119238230643840 : Int) atom2385) := by
  rw [SparsePolynomial.eval_scale, eval_atom2385]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2386 : SparsePolynomial.Poly := [([13,19,20], 1)]
theorem eval_atom2386 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2386 = ((g 13) * (g 19) * (g 20)) := by
  norm_num [atom2386, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2386_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (537665600102400 : Int) atom2386) := by
  rw [SparsePolynomial.eval_scale, eval_atom2386]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2387 : SparsePolynomial.Poly := [([13,19,21], 1)]
theorem eval_atom2387 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2387 = ((g 13) * (g 19) * (g 21)) := by
  norm_num [atom2387, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2387_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (648792328060800 : Int) atom2387) := by
  rw [SparsePolynomial.eval_scale, eval_atom2387]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2388 : SparsePolynomial.Poly := [([13,19,22], 1)]
theorem eval_atom2388 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2388 = ((g 13) * (g 19) * (g 22)) := by
  norm_num [atom2388, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2388_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (516707405222400 : Int) atom2388) := by
  rw [SparsePolynomial.eval_scale, eval_atom2388]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2389 : SparsePolynomial.Poly := [([13,19,23], 1)]
theorem eval_atom2389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2389 = ((g 13) * (g 19) * (g 23)) := by
  norm_num [atom2389, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (684584938699200 : Int) atom2389) := by
  rw [SparsePolynomial.eval_scale, eval_atom2389]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2390 : SparsePolynomial.Poly := [([13,20,20], 1)]
theorem eval_atom2390 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2390 = ((g 13) * (g 20) * (g 20)) := by
  norm_num [atom2390, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2390_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (392272304054400 : Int) atom2390) := by
  rw [SparsePolynomial.eval_scale, eval_atom2390]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2391 : SparsePolynomial.Poly := [([13,20,21], 1)]
theorem eval_atom2391 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2391 = ((g 13) * (g 20) * (g 21)) := by
  norm_num [atom2391, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2391_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (772722742176000 : Int) atom2391) := by
  rw [SparsePolynomial.eval_scale, eval_atom2391]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2392 : SparsePolynomial.Poly := [([13,20,22], 1)]
theorem eval_atom2392 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2392 = ((g 13) * (g 20) * (g 22)) := by
  norm_num [atom2392, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2392_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (564667693430400 : Int) atom2392) := by
  rw [SparsePolynomial.eval_scale, eval_atom2392]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2393 : SparsePolynomial.Poly := [([13,20,23], 1)]
theorem eval_atom2393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2393 = ((g 13) * (g 20) * (g 23)) := by
  norm_num [atom2393, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (540935936956800 : Int) atom2393) := by
  rw [SparsePolynomial.eval_scale, eval_atom2393]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2394 : SparsePolynomial.Poly := [([13,21,21], 1)]
theorem eval_atom2394 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2394 = ((g 13) * (g 21) * (g 21)) := by
  norm_num [atom2394, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2394_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (337287870057600 : Int) atom2394) := by
  rw [SparsePolynomial.eval_scale, eval_atom2394]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2395 : SparsePolynomial.Poly := [([13,21,22], 1)]
theorem eval_atom2395 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2395 = ((g 13) * (g 21) * (g 22)) := by
  norm_num [atom2395, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2395_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (504358789233600 : Int) atom2395) := by
  rw [SparsePolynomial.eval_scale, eval_atom2395]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2396 : SparsePolynomial.Poly := [([13,21,23], 1)]
theorem eval_atom2396 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2396 = ((g 13) * (g 21) * (g 23)) := by
  norm_num [atom2396, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2396_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (508847144097600 : Int) atom2396) := by
  rw [SparsePolynomial.eval_scale, eval_atom2396]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2397 : SparsePolynomial.Poly := [([13,22,22], 1)]
theorem eval_atom2397 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2397 = ((g 13) * (g 22) * (g 22)) := by
  norm_num [atom2397, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2397_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121844922595200 : Int) atom2397) := by
  rw [SparsePolynomial.eval_scale, eval_atom2397]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2398 : SparsePolynomial.Poly := [([13,22,23], 1)]
theorem eval_atom2398 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2398 = ((g 13) * (g 22) * (g 23)) := by
  norm_num [atom2398, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2398_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (265838402340000 : Int) atom2398) := by
  rw [SparsePolynomial.eval_scale, eval_atom2398]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2399 : SparsePolynomial.Poly := [([13,23,23], 1)]
theorem eval_atom2399 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2399 = ((g 13) * (g 23) * (g 23)) := by
  norm_num [atom2399, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2399_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109034705656800 : Int) atom2399) := by
  rw [SparsePolynomial.eval_scale, eval_atom2399]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2400 : SparsePolynomial.Poly := [([14,14,14], 1)]
theorem eval_atom2400 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2400 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom2400, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2400_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2739299270400 : Int) atom2400) := by
  rw [SparsePolynomial.eval_scale, eval_atom2400]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2401 : SparsePolynomial.Poly := [([14,14,18], 1)]
theorem eval_atom2401 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2401 = ((g 14) * (g 14) * (g 18)) := by
  norm_num [atom2401, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2401_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20400780708000 : Int) atom2401) := by
  rw [SparsePolynomial.eval_scale, eval_atom2401]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2402 : SparsePolynomial.Poly := [([14,14,20], 1)]
theorem eval_atom2402 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2402 = ((g 14) * (g 14) * (g 20)) := by
  norm_num [atom2402, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2402_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52121547324000 : Int) atom2402) := by
  rw [SparsePolynomial.eval_scale, eval_atom2402]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2403 : SparsePolynomial.Poly := [([14,14,21], 1)]
theorem eval_atom2403 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2403 = ((g 14) * (g 14) * (g 21)) := by
  norm_num [atom2403, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2403_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12579780074400 : Int) atom2403) := by
  rw [SparsePolynomial.eval_scale, eval_atom2403]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2404 : SparsePolynomial.Poly := [([14,15,15], 1)]
theorem eval_atom2404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2404 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom2404, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5134857235200 : Int) atom2404) := by
  rw [SparsePolynomial.eval_scale, eval_atom2404]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2405 : SparsePolynomial.Poly := [([14,15,17], 1)]
theorem eval_atom2405 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2405 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom2405, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2405_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3083040576000 : Int) atom2405) := by
  rw [SparsePolynomial.eval_scale, eval_atom2405]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2406 : SparsePolynomial.Poly := [([14,15,18], 1)]
theorem eval_atom2406 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2406 = ((g 14) * (g 15) * (g 18)) := by
  norm_num [atom2406, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2406_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39376524972960 : Int) atom2406) := by
  rw [SparsePolynomial.eval_scale, eval_atom2406]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2407 : SparsePolynomial.Poly := [([14,15,20], 1)]
theorem eval_atom2407 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2407 = ((g 14) * (g 15) * (g 20)) := by
  norm_num [atom2407, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2407_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (174486042511200 : Int) atom2407) := by
  rw [SparsePolynomial.eval_scale, eval_atom2407]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2408 : SparsePolynomial.Poly := [([14,15,21], 1)]
theorem eval_atom2408 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2408 = ((g 14) * (g 15) * (g 21)) := by
  norm_num [atom2408, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2408_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (128607934240800 : Int) atom2408) := by
  rw [SparsePolynomial.eval_scale, eval_atom2408]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2409 : SparsePolynomial.Poly := [([14,15,22], 1)]
theorem eval_atom2409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2409 = ((g 14) * (g 15) * (g 22)) := by
  norm_num [atom2409, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96386479580160 : Int) atom2409) := by
  rw [SparsePolynomial.eval_scale, eval_atom2409]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2410 : SparsePolynomial.Poly := [([14,15,23], 1)]
theorem eval_atom2410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2410 = ((g 14) * (g 15) * (g 23)) := by
  norm_num [atom2410, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153439015262400 : Int) atom2410) := by
  rw [SparsePolynomial.eval_scale, eval_atom2410]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2411 : SparsePolynomial.Poly := [([14,16,16], 1)]
theorem eval_atom2411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2411 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom2411, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11300938387200 : Int) atom2411) := by
  rw [SparsePolynomial.eval_scale, eval_atom2411]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2412 : SparsePolynomial.Poly := [([14,16,17], 1)]
theorem eval_atom2412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2412 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom2412, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24664324608000 : Int) atom2412) := by
  rw [SparsePolynomial.eval_scale, eval_atom2412]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2413 : SparsePolynomial.Poly := [([14,16,18], 1)]
theorem eval_atom2413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2413 = ((g 14) * (g 16) * (g 18)) := by
  norm_num [atom2413, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27029092436640 : Int) atom2413) := by
  rw [SparsePolynomial.eval_scale, eval_atom2413]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2414 : SparsePolynomial.Poly := [([14,16,20], 1)]
theorem eval_atom2414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2414 = ((g 14) * (g 16) * (g 20)) := by
  norm_num [atom2414, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (215567799804000 : Int) atom2414) := by
  rw [SparsePolynomial.eval_scale, eval_atom2414]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2415 : SparsePolynomial.Poly := [([14,16,21], 1)]
theorem eval_atom2415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2415 = ((g 14) * (g 16) * (g 21)) := by
  norm_num [atom2415, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197885015748000 : Int) atom2415) := by
  rw [SparsePolynomial.eval_scale, eval_atom2415]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2416 : SparsePolynomial.Poly := [([14,16,22], 1)]
theorem eval_atom2416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2416 = ((g 14) * (g 16) * (g 22)) := by
  norm_num [atom2416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164800213079040 : Int) atom2416) := by
  rw [SparsePolynomial.eval_scale, eval_atom2416]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2417 : SparsePolynomial.Poly := [([14,16,23], 1)]
theorem eval_atom2417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2417 = ((g 14) * (g 16) * (g 23)) := by
  norm_num [atom2417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (363241134547200 : Int) atom2417) := by
  rw [SparsePolynomial.eval_scale, eval_atom2417]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2418 : SparsePolynomial.Poly := [([14,17,17], 1)]
theorem eval_atom2418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2418 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom2418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25008065913600 : Int) atom2418) := by
  rw [SparsePolynomial.eval_scale, eval_atom2418]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2419 : SparsePolynomial.Poly := [([14,17,18], 1)]
theorem eval_atom2419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2419 = ((g 14) * (g 17) * (g 18)) := by
  norm_num [atom2419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71475157353600 : Int) atom2419) := by
  rw [SparsePolynomial.eval_scale, eval_atom2419]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2420 : SparsePolynomial.Poly := [([14,17,19], 1)]
theorem eval_atom2420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2420 = ((g 14) * (g 17) * (g 19)) := by
  norm_num [atom2420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89689459860000 : Int) atom2420) := by
  rw [SparsePolynomial.eval_scale, eval_atom2420]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2421 : SparsePolynomial.Poly := [([14,17,20], 1)]
theorem eval_atom2421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2421 = ((g 14) * (g 17) * (g 20)) := by
  norm_num [atom2421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (351305386185600 : Int) atom2421) := by
  rw [SparsePolynomial.eval_scale, eval_atom2421]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2422 : SparsePolynomial.Poly := [([14,17,21], 1)]
theorem eval_atom2422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2422 = ((g 14) * (g 17) * (g 21)) := by
  norm_num [atom2422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (364301110958400 : Int) atom2422) := by
  rw [SparsePolynomial.eval_scale, eval_atom2422]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2423 : SparsePolynomial.Poly := [([14,17,22], 1)]
theorem eval_atom2423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2423 = ((g 14) * (g 17) * (g 22)) := by
  norm_num [atom2423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (361575865778400 : Int) atom2423) := by
  rw [SparsePolynomial.eval_scale, eval_atom2423]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2424 : SparsePolynomial.Poly := [([14,17,23], 1)]
theorem eval_atom2424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2424 = ((g 14) * (g 17) * (g 23)) := by
  norm_num [atom2424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (584217584596800 : Int) atom2424) := by
  rw [SparsePolynomial.eval_scale, eval_atom2424]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2425 : SparsePolynomial.Poly := [([14,18,18], 1)]
theorem eval_atom2425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2425 = ((g 14) * (g 18) * (g 18)) := by
  norm_num [atom2425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89642062540800 : Int) atom2425) := by
  rw [SparsePolynomial.eval_scale, eval_atom2425]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2426 : SparsePolynomial.Poly := [([14,18,19], 1)]
theorem eval_atom2426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2426 = ((g 14) * (g 18) * (g 19)) := by
  norm_num [atom2426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (231081643069200 : Int) atom2426) := by
  rw [SparsePolynomial.eval_scale, eval_atom2426]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2427 : SparsePolynomial.Poly := [([14,18,20], 1)]
theorem eval_atom2427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2427 = ((g 14) * (g 18) * (g 20)) := by
  norm_num [atom2427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (545421771417600 : Int) atom2427) := by
  rw [SparsePolynomial.eval_scale, eval_atom2427]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2428 : SparsePolynomial.Poly := [([14,18,21], 1)]
theorem eval_atom2428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2428 = ((g 14) * (g 18) * (g 21)) := by
  norm_num [atom2428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (587648796134400 : Int) atom2428) := by
  rw [SparsePolynomial.eval_scale, eval_atom2428]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2429 : SparsePolynomial.Poly := [([14,18,22], 1)]
theorem eval_atom2429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2429 = ((g 14) * (g 18) * (g 22)) := by
  norm_num [atom2429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (482552368527600 : Int) atom2429) := by
  rw [SparsePolynomial.eval_scale, eval_atom2429]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2430 : SparsePolynomial.Poly := [([14,18,23], 1)]
theorem eval_atom2430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2430 = ((g 14) * (g 18) * (g 23)) := by
  norm_num [atom2430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (759227313121200 : Int) atom2430) := by
  rw [SparsePolynomial.eval_scale, eval_atom2430]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2431 : SparsePolynomial.Poly := [([14,19,19], 1)]
theorem eval_atom2431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2431 = ((g 14) * (g 19) * (g 19)) := by
  norm_num [atom2431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (95421168944640 : Int) atom2431) := by
  rw [SparsePolynomial.eval_scale, eval_atom2431]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2432 : SparsePolynomial.Poly := [([14,19,20], 1)]
theorem eval_atom2432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2432 = ((g 14) * (g 19) * (g 20)) := by
  norm_num [atom2432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (500895976719600 : Int) atom2432) := by
  rw [SparsePolynomial.eval_scale, eval_atom2432]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2433 : SparsePolynomial.Poly := [([14,19,21], 1)]
theorem eval_atom2433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2433 = ((g 14) * (g 19) * (g 21)) := by
  norm_num [atom2433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (624067545162600 : Int) atom2433) := by
  rw [SparsePolynomial.eval_scale, eval_atom2433]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2434 : SparsePolynomial.Poly := [([14,19,22], 1)]
theorem eval_atom2434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2434 = ((g 14) * (g 19) * (g 22)) := by
  norm_num [atom2434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (528698249503200 : Int) atom2434) := by
  rw [SparsePolynomial.eval_scale, eval_atom2434]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2435 : SparsePolynomial.Poly := [([14,19,23], 1)]
theorem eval_atom2435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2435 = ((g 14) * (g 19) * (g 23)) := by
  norm_num [atom2435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (709210793699100 : Int) atom2435) := by
  rw [SparsePolynomial.eval_scale, eval_atom2435]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2436 : SparsePolynomial.Poly := [([14,20,20], 1)]
theorem eval_atom2436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2436 = ((g 14) * (g 20) * (g 20)) := by
  norm_num [atom2436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (378597382732800 : Int) atom2436) := by
  rw [SparsePolynomial.eval_scale, eval_atom2436]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2437 : SparsePolynomial.Poly := [([14,20,21], 1)]
theorem eval_atom2437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2437 = ((g 14) * (g 20) * (g 21)) := by
  norm_num [atom2437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (759618673228800 : Int) atom2437) := by
  rw [SparsePolynomial.eval_scale, eval_atom2437]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2438 : SparsePolynomial.Poly := [([14,20,22], 1)]
theorem eval_atom2438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2438 = ((g 14) * (g 20) * (g 22)) := by
  norm_num [atom2438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (613004972605200 : Int) atom2438) := by
  rw [SparsePolynomial.eval_scale, eval_atom2438]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2439 : SparsePolynomial.Poly := [([14,20,23], 1)]
theorem eval_atom2439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2439 = ((g 14) * (g 20) * (g 23)) := by
  norm_num [atom2439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (656760067563600 : Int) atom2439) := by
  rw [SparsePolynomial.eval_scale, eval_atom2439]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2440 : SparsePolynomial.Poly := [([14,21,21], 1)]
theorem eval_atom2440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2440 = ((g 14) * (g 21) * (g 21)) := by
  norm_num [atom2440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (334775681856000 : Int) atom2440) := by
  rw [SparsePolynomial.eval_scale, eval_atom2440]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2441 : SparsePolynomial.Poly := [([14,21,22], 1)]
theorem eval_atom2441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2441 = ((g 14) * (g 21) * (g 22)) := by
  norm_num [atom2441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (573058747560600 : Int) atom2441) := by
  rw [SparsePolynomial.eval_scale, eval_atom2441]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2442 : SparsePolynomial.Poly := [([14,21,23], 1)]
theorem eval_atom2442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2442 = ((g 14) * (g 21) * (g 23)) := by
  norm_num [atom2442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (648004298772600 : Int) atom2442) := by
  rw [SparsePolynomial.eval_scale, eval_atom2442]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2443 : SparsePolynomial.Poly := [([14,22,22], 1)]
theorem eval_atom2443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2443 = ((g 14) * (g 22) * (g 22)) := by
  norm_num [atom2443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188901029066400 : Int) atom2443) := by
  rw [SparsePolynomial.eval_scale, eval_atom2443]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2444 : SparsePolynomial.Poly := [([14,22,23], 1)]
theorem eval_atom2444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2444 = ((g 14) * (g 22) * (g 23)) := by
  norm_num [atom2444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (479009353479300 : Int) atom2444) := by
  rw [SparsePolynomial.eval_scale, eval_atom2444]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2445 : SparsePolynomial.Poly := [([14,23,23], 1)]
theorem eval_atom2445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2445 = ((g 14) * (g 23) * (g 23)) := by
  norm_num [atom2445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (253041385835700 : Int) atom2445) := by
  rw [SparsePolynomial.eval_scale, eval_atom2445]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2446 : SparsePolynomial.Poly := [([15,15,15], 1)]
theorem eval_atom2446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2446 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom2446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4450918348800 : Int) atom2446) := by
  rw [SparsePolynomial.eval_scale, eval_atom2446]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2447 : SparsePolynomial.Poly := [([15,15,18], 1)]
theorem eval_atom2447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2447 = ((g 15) * (g 15) * (g 18)) := by
  norm_num [atom2447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24318972518400 : Int) atom2447) := by
  rw [SparsePolynomial.eval_scale, eval_atom2447]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2448 : SparsePolynomial.Poly := [([15,15,20], 1)]
theorem eval_atom2448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2448 = ((g 15) * (g 15) * (g 20)) := by
  norm_num [atom2448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89482272768000 : Int) atom2448) := by
  rw [SparsePolynomial.eval_scale, eval_atom2448]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block032 : SparsePolynomial.Poly := [([13,16,21], 268132862289600), ([13,16,22], 255013789363200), ([13,16,23], 456770220228000), ([13,17,17], 41470439472000), ([13,17,18], 130081695004800), ([13,17,19], 144679235500800), ([13,17,20], 412121123568000), ([13,17,21], 420077150539200), ([13,17,22], 432690996326400), ([13,17,23], 655019877204000), ([13,18,18], 122580671875200), ([13,18,19], 282393592588800), ([13,18,20], 586889813664000), ([13,18,21], 616912250169600), ([13,18,22], 497465235388800), ([13,18,23], 765835096118400), ([13,19,19], 119238230643840), ([13,19,20], 537665600102400), ([13,19,21], 648792328060800), ([13,19,22], 516707405222400), ([13,19,23], 684584938699200), ([13,20,20], 392272304054400), ([13,20,21], 772722742176000), ([13,20,22], 564667693430400), ([13,20,23], 540935936956800), ([13,21,21], 337287870057600), ([13,21,22], 504358789233600), ([13,21,23], 508847144097600), ([13,22,22], 121844922595200), ([13,22,23], 265838402340000), ([13,23,23], 109034705656800), ([14,14,14], 2739299270400), ([14,14,18], 20400780708000), ([14,14,20], 52121547324000), ([14,14,21], 12579780074400), ([14,15,15], 5134857235200), ([14,15,17], 3083040576000), ([14,15,18], 39376524972960), ([14,15,20], 174486042511200), ([14,15,21], 128607934240800), ([14,15,22], 96386479580160), ([14,15,23], 153439015262400), ([14,16,16], 11300938387200), ([14,16,17], 24664324608000), ([14,16,18], 27029092436640), ([14,16,20], 215567799804000), ([14,16,21], 197885015748000), ([14,16,22], 164800213079040), ([14,16,23], 363241134547200), ([14,17,17], 25008065913600), ([14,17,18], 71475157353600), ([14,17,19], 89689459860000), ([14,17,20], 351305386185600), ([14,17,21], 364301110958400), ([14,17,22], 361575865778400), ([14,17,23], 584217584596800), ([14,18,18], 89642062540800), ([14,18,19], 231081643069200), ([14,18,20], 545421771417600), ([14,18,21], 587648796134400), ([14,18,22], 482552368527600), ([14,18,23], 759227313121200), ([14,19,19], 95421168944640), ([14,19,20], 500895976719600), ([14,19,21], 624067545162600), ([14,19,22], 528698249503200), ([14,19,23], 709210793699100), ([14,20,20], 378597382732800), ([14,20,21], 759618673228800), ([14,20,22], 613004972605200), ([14,20,23], 656760067563600), ([14,21,21], 334775681856000), ([14,21,22], 573058747560600), ([14,21,23], 648004298772600), ([14,22,22], 188901029066400), ([14,22,23], 479009353479300), ([14,23,23], 253041385835700), ([15,15,15], 4450918348800), ([15,15,18], 24318972518400), ([15,15,20], 89482272768000)]
theorem block032_data : block032 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (268132862289600 : Int) atom2369) (SparsePolynomial.scale (255013789363200 : Int) atom2370)) (SparsePolynomial.merge (SparsePolynomial.scale (456770220228000 : Int) atom2371) (SparsePolynomial.merge (SparsePolynomial.scale (41470439472000 : Int) atom2372) (SparsePolynomial.scale (130081695004800 : Int) atom2373)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (144679235500800 : Int) atom2374) (SparsePolynomial.scale (412121123568000 : Int) atom2375)) (SparsePolynomial.merge (SparsePolynomial.scale (420077150539200 : Int) atom2376) (SparsePolynomial.merge (SparsePolynomial.scale (432690996326400 : Int) atom2377) (SparsePolynomial.scale (655019877204000 : Int) atom2378))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (122580671875200 : Int) atom2379) (SparsePolynomial.scale (282393592588800 : Int) atom2380)) (SparsePolynomial.merge (SparsePolynomial.scale (586889813664000 : Int) atom2381) (SparsePolynomial.merge (SparsePolynomial.scale (616912250169600 : Int) atom2382) (SparsePolynomial.scale (497465235388800 : Int) atom2383)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (765835096118400 : Int) atom2384) (SparsePolynomial.scale (119238230643840 : Int) atom2385)) (SparsePolynomial.merge (SparsePolynomial.scale (537665600102400 : Int) atom2386) (SparsePolynomial.merge (SparsePolynomial.scale (648792328060800 : Int) atom2387) (SparsePolynomial.scale (516707405222400 : Int) atom2388)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (684584938699200 : Int) atom2389) (SparsePolynomial.scale (392272304054400 : Int) atom2390)) (SparsePolynomial.merge (SparsePolynomial.scale (772722742176000 : Int) atom2391) (SparsePolynomial.merge (SparsePolynomial.scale (564667693430400 : Int) atom2392) (SparsePolynomial.scale (540935936956800 : Int) atom2393)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (337287870057600 : Int) atom2394) (SparsePolynomial.scale (504358789233600 : Int) atom2395)) (SparsePolynomial.merge (SparsePolynomial.scale (508847144097600 : Int) atom2396) (SparsePolynomial.merge (SparsePolynomial.scale (121844922595200 : Int) atom2397) (SparsePolynomial.scale (265838402340000 : Int) atom2398))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (109034705656800 : Int) atom2399) (SparsePolynomial.scale (2739299270400 : Int) atom2400)) (SparsePolynomial.merge (SparsePolynomial.scale (20400780708000 : Int) atom2401) (SparsePolynomial.merge (SparsePolynomial.scale (52121547324000 : Int) atom2402) (SparsePolynomial.scale (12579780074400 : Int) atom2403)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5134857235200 : Int) atom2404) (SparsePolynomial.scale (3083040576000 : Int) atom2405)) (SparsePolynomial.merge (SparsePolynomial.scale (39376524972960 : Int) atom2406) (SparsePolynomial.merge (SparsePolynomial.scale (174486042511200 : Int) atom2407) (SparsePolynomial.scale (128607934240800 : Int) atom2408))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (96386479580160 : Int) atom2409) (SparsePolynomial.scale (153439015262400 : Int) atom2410)) (SparsePolynomial.merge (SparsePolynomial.scale (11300938387200 : Int) atom2411) (SparsePolynomial.merge (SparsePolynomial.scale (24664324608000 : Int) atom2412) (SparsePolynomial.scale (27029092436640 : Int) atom2413)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (215567799804000 : Int) atom2414) (SparsePolynomial.scale (197885015748000 : Int) atom2415)) (SparsePolynomial.merge (SparsePolynomial.scale (164800213079040 : Int) atom2416) (SparsePolynomial.merge (SparsePolynomial.scale (363241134547200 : Int) atom2417) (SparsePolynomial.scale (25008065913600 : Int) atom2418))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (71475157353600 : Int) atom2419) (SparsePolynomial.scale (89689459860000 : Int) atom2420)) (SparsePolynomial.merge (SparsePolynomial.scale (351305386185600 : Int) atom2421) (SparsePolynomial.merge (SparsePolynomial.scale (364301110958400 : Int) atom2422) (SparsePolynomial.scale (361575865778400 : Int) atom2423)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (584217584596800 : Int) atom2424) (SparsePolynomial.scale (89642062540800 : Int) atom2425)) (SparsePolynomial.merge (SparsePolynomial.scale (231081643069200 : Int) atom2426) (SparsePolynomial.merge (SparsePolynomial.scale (545421771417600 : Int) atom2427) (SparsePolynomial.scale (587648796134400 : Int) atom2428)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (482552368527600 : Int) atom2429) (SparsePolynomial.scale (759227313121200 : Int) atom2430)) (SparsePolynomial.merge (SparsePolynomial.scale (95421168944640 : Int) atom2431) (SparsePolynomial.merge (SparsePolynomial.scale (500895976719600 : Int) atom2432) (SparsePolynomial.scale (624067545162600 : Int) atom2433)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (528698249503200 : Int) atom2434) (SparsePolynomial.scale (709210793699100 : Int) atom2435)) (SparsePolynomial.merge (SparsePolynomial.scale (378597382732800 : Int) atom2436) (SparsePolynomial.merge (SparsePolynomial.scale (759618673228800 : Int) atom2437) (SparsePolynomial.scale (613004972605200 : Int) atom2438))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (656760067563600 : Int) atom2439) (SparsePolynomial.scale (334775681856000 : Int) atom2440)) (SparsePolynomial.merge (SparsePolynomial.scale (573058747560600 : Int) atom2441) (SparsePolynomial.merge (SparsePolynomial.scale (648004298772600 : Int) atom2442) (SparsePolynomial.scale (188901029066400 : Int) atom2443)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (479009353479300 : Int) atom2444) (SparsePolynomial.scale (253041385835700 : Int) atom2445)) (SparsePolynomial.merge (SparsePolynomial.scale (4450918348800 : Int) atom2446) (SparsePolynomial.merge (SparsePolynomial.scale (24318972518400 : Int) atom2447) (SparsePolynomial.scale (89482272768000 : Int) atom2448)))))))) := by decide +kernel
theorem block032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block032 := by
  rw [block032_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2369_nonneg g hg hA hB) (atom2370_nonneg g hg hA hB)) (add_nonneg (atom2371_nonneg g hg hA hB) (add_nonneg (atom2372_nonneg g hg hA hB) (atom2373_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2374_nonneg g hg hA hB) (atom2375_nonneg g hg hA hB)) (add_nonneg (atom2376_nonneg g hg hA hB) (add_nonneg (atom2377_nonneg g hg hA hB) (atom2378_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2379_nonneg g hg hA hB) (atom2380_nonneg g hg hA hB)) (add_nonneg (atom2381_nonneg g hg hA hB) (add_nonneg (atom2382_nonneg g hg hA hB) (atom2383_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2384_nonneg g hg hA hB) (atom2385_nonneg g hg hA hB)) (add_nonneg (atom2386_nonneg g hg hA hB) (add_nonneg (atom2387_nonneg g hg hA hB) (atom2388_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2389_nonneg g hg hA hB) (atom2390_nonneg g hg hA hB)) (add_nonneg (atom2391_nonneg g hg hA hB) (add_nonneg (atom2392_nonneg g hg hA hB) (atom2393_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2394_nonneg g hg hA hB) (atom2395_nonneg g hg hA hB)) (add_nonneg (atom2396_nonneg g hg hA hB) (add_nonneg (atom2397_nonneg g hg hA hB) (atom2398_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2399_nonneg g hg hA hB) (atom2400_nonneg g hg hA hB)) (add_nonneg (atom2401_nonneg g hg hA hB) (add_nonneg (atom2402_nonneg g hg hA hB) (atom2403_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2404_nonneg g hg hA hB) (atom2405_nonneg g hg hA hB)) (add_nonneg (atom2406_nonneg g hg hA hB) (add_nonneg (atom2407_nonneg g hg hA hB) (atom2408_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2409_nonneg g hg hA hB) (atom2410_nonneg g hg hA hB)) (add_nonneg (atom2411_nonneg g hg hA hB) (add_nonneg (atom2412_nonneg g hg hA hB) (atom2413_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2414_nonneg g hg hA hB) (atom2415_nonneg g hg hA hB)) (add_nonneg (atom2416_nonneg g hg hA hB) (add_nonneg (atom2417_nonneg g hg hA hB) (atom2418_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2419_nonneg g hg hA hB) (atom2420_nonneg g hg hA hB)) (add_nonneg (atom2421_nonneg g hg hA hB) (add_nonneg (atom2422_nonneg g hg hA hB) (atom2423_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2424_nonneg g hg hA hB) (atom2425_nonneg g hg hA hB)) (add_nonneg (atom2426_nonneg g hg hA hB) (add_nonneg (atom2427_nonneg g hg hA hB) (atom2428_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2429_nonneg g hg hA hB) (atom2430_nonneg g hg hA hB)) (add_nonneg (atom2431_nonneg g hg hA hB) (add_nonneg (atom2432_nonneg g hg hA hB) (atom2433_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2434_nonneg g hg hA hB) (atom2435_nonneg g hg hA hB)) (add_nonneg (atom2436_nonneg g hg hA hB) (add_nonneg (atom2437_nonneg g hg hA hB) (atom2438_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2439_nonneg g hg hA hB) (atom2440_nonneg g hg hA hB)) (add_nonneg (atom2441_nonneg g hg hA hB) (add_nonneg (atom2442_nonneg g hg hA hB) (atom2443_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2444_nonneg g hg hA hB) (atom2445_nonneg g hg hA hB)) (add_nonneg (atom2446_nonneg g hg hA hB) (add_nonneg (atom2447_nonneg g hg hA hB) (atom2448_nonneg g hg hA hB))))))))

end APPT.Finite24
