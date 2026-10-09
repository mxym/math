import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0393 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0393 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0393 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0393_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35700480 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394 : SparsePolynomial.Poly := [([3,6,9], 1)]
theorem eval_atom0394 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0394 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0394_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72161280 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395 : SparsePolynomial.Poly := [([3,6,10], 1)]
theorem eval_atom0395 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0395 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0395_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50591520 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396 : SparsePolynomial.Poly := [([3,6,11], 1)]
theorem eval_atom0396 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0396 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0396_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70005600 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397 : SparsePolynomial.Poly := [([3,6,12], 1)]
theorem eval_atom0397 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0397 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0397_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76122720 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398 : SparsePolynomial.Poly := [([3,6,13], 1)]
theorem eval_atom0398 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0398 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0398_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (92435040 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399 : SparsePolynomial.Poly := [([3,6,14], 1)]
theorem eval_atom0399 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0399 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0399_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108747360 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0400 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0400 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0400_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25864320 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0401 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0401 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0401_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52137600 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402 : SparsePolynomial.Poly := [([3,7,9], 1)]
theorem eval_atom0402 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0402 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0402_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82087680 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403 : SparsePolynomial.Poly := [([3,7,10], 1)]
theorem eval_atom0403 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0403 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0403_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64683600 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404 : SparsePolynomial.Poly := [([3,7,11], 1)]
theorem eval_atom0404 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0404 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0404_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (87060960 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405 : SparsePolynomial.Poly := [([3,7,12], 1)]
theorem eval_atom0405 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0405 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0405_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89438640 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406 : SparsePolynomial.Poly := [([3,7,13], 1)]
theorem eval_atom0406 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0406 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0406_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105904560 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407 : SparsePolynomial.Poly := [([3,7,14], 1)]
theorem eval_atom0407 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0407 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0407_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (122426640 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0408 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0408 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0408_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36201600 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409 : SparsePolynomial.Poly := [([3,8,9], 1)]
theorem eval_atom0409 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0409 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0409_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99174240 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410 : SparsePolynomial.Poly := [([3,8,10], 1)]
theorem eval_atom0410 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0410 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0410_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78505200 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411 : SparsePolynomial.Poly := [([3,8,11], 1)]
theorem eval_atom0411 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0411 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0411_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104116320 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412 : SparsePolynomial.Poly := [([3,8,12], 1)]
theorem eval_atom0412 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0412 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0412_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105652080 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413 : SparsePolynomial.Poly := [([3,8,13], 1)]
theorem eval_atom0413 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0413 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0413_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109812240 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414 : SparsePolynomial.Poly := [([3,8,14], 1)]
theorem eval_atom0414 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0414 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0414_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153509040 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom0415 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0415 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0415_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74908800 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416 : SparsePolynomial.Poly := [([3,9,10], 1)]
theorem eval_atom0416 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0416 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0416_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (124263720 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417 : SparsePolynomial.Poly := [([3,9,11], 1)]
theorem eval_atom0417 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0417 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0417_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (176277600 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418 : SparsePolynomial.Poly := [([3,9,12], 1)]
theorem eval_atom0418 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0418 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0418_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (180672120 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419 : SparsePolynomial.Poly := [([3,9,13], 1)]
theorem eval_atom0419 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0419 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0419_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (113707800 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420 : SparsePolynomial.Poly := [([3,9,14], 1)]
theorem eval_atom0420 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0420 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0420_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (182823480 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom0421 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0421 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0421_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57262464 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422 : SparsePolynomial.Poly := [([3,10,11], 1)]
theorem eval_atom0422 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0422 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0422_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145208160 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423 : SparsePolynomial.Poly := [([3,10,12], 1)]
theorem eval_atom0423 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0423 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0423_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171628740 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424 : SparsePolynomial.Poly := [([3,10,13], 1)]
theorem eval_atom0424 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0424 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0424_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121886640 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425 : SparsePolynomial.Poly := [([3,10,14], 1)]
theorem eval_atom0425 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0425 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0425_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (154082790 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom0426 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0426 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0426_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98175240 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427 : SparsePolynomial.Poly := [([3,11,12], 1)]
theorem eval_atom0427 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0427 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0427_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171553680 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428 : SparsePolynomial.Poly := [([3,11,13], 1)]
theorem eval_atom0428 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0428 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0428_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120222360 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429 : SparsePolynomial.Poly := [([3,11,14], 1)]
theorem eval_atom0429 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0429 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0429_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170511480 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430 : SparsePolynomial.Poly := [([3,12,12], 1)]
theorem eval_atom0430 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0430 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0430_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64707660 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431 : SparsePolynomial.Poly := [([3,12,13], 1)]
theorem eval_atom0431 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0431 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0431_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (94666860 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432 : SparsePolynomial.Poly := [([3,12,14], 1)]
theorem eval_atom0432 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0432 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0432_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (155708190 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433 : SparsePolynomial.Poly := [([3,13,13], 1)]
theorem eval_atom0433 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0433 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0433_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15264720 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434 : SparsePolynomial.Poly := [([3,13,14], 1)]
theorem eval_atom0434 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0434 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0434_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99311130 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435 : SparsePolynomial.Poly := [([3,14,14], 1)]
theorem eval_atom0435 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0435 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0435_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79701570 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0436 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0436 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0436_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2931840 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437 : SparsePolynomial.Poly := [([4,4,9], 1)]
theorem eval_atom0437 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0437 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0437_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19845360 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438 : SparsePolynomial.Poly := [([4,4,11], 1)]
theorem eval_atom0438 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0438 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0438_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221760 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439 : SparsePolynomial.Poly := [([4,5,7], 1)]
theorem eval_atom0439 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0439 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0439_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1900800 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440 : SparsePolynomial.Poly := [([4,5,8], 1)]
theorem eval_atom0440 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0440 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0440_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3801600 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441 : SparsePolynomial.Poly := [([4,5,9], 1)]
theorem eval_atom0441 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0441 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0441_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33785280 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom0442 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0442 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0442_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4849920 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom0443 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0443 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0443_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11026080 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444 : SparsePolynomial.Poly := [([4,5,12], 1)]
theorem eval_atom0444 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0444 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0444_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22376160 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445 : SparsePolynomial.Poly := [([4,5,13], 1)]
theorem eval_atom0445 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0445 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0445_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37272960 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446 : SparsePolynomial.Poly := [([4,5,14], 1)]
theorem eval_atom0446 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0446 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0446_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54092880 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0447 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0447 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0447_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5466240 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0448 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0448 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0448_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13541760 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0449 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0449 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0449_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16151040 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom0450 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0450 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0450_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42252480 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom0451 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0451 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0451_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23506560 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom0452 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0452 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0452_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33835680 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453 : SparsePolynomial.Poly := [([4,6,12], 1)]
theorem eval_atom0453 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0453 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0453_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49206240 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454 : SparsePolynomial.Poly := [([4,6,13], 1)]
theorem eval_atom0454 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0454 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0454_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68711040 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455 : SparsePolynomial.Poly := [([4,6,14], 1)]
theorem eval_atom0455 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0455 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0455_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89836560 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0456 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0456 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0456_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14188800 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0457 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0457 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0457_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30462720 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom0458 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0458 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0458_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52680000 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom0459 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0459 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0459_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40726320 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom0460 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0460 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0460_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56645280 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461 : SparsePolynomial.Poly := [([4,7,12], 1)]
theorem eval_atom0461 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0461 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0461_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70185840 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462 : SparsePolynomial.Poly := [([4,7,13], 1)]
theorem eval_atom0462 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0462 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0462_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91753680 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463 : SparsePolynomial.Poly := [([4,7,14], 1)]
theorem eval_atom0463 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0463 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0463_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114639840 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0464 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0464 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0464_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24301440 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465 : SparsePolynomial.Poly := [([4,8,9], 1)]
theorem eval_atom0465 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0465 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0465_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70267680 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466 : SparsePolynomial.Poly := [([4,8,10], 1)]
theorem eval_atom0466 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0466 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0466_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57675600 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467 : SparsePolynomial.Poly := [([4,8,11], 1)]
theorem eval_atom0467 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0467 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0467_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79454880 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468 : SparsePolynomial.Poly := [([4,8,12], 1)]
theorem eval_atom0468 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0468 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0468_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (94062960 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469 : SparsePolynomial.Poly := [([4,8,13], 1)]
theorem eval_atom0469 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0469 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0469_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105234480 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470 : SparsePolynomial.Poly := [([4,8,14], 1)]
theorem eval_atom0470 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0470 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0470_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156846240 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom0471 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0471 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0471_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59616000 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472 : SparsePolynomial.Poly := [([4,9,10], 1)]
theorem eval_atom0472 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0472 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0472_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103584600 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block005 : SparsePolynomial.Poly := [([3,6,8], 35700480), ([3,6,9], 72161280), ([3,6,10], 50591520), ([3,6,11], 70005600), ([3,6,12], 76122720), ([3,6,13], 92435040), ([3,6,14], 108747360), ([3,7,7], 25864320), ([3,7,8], 52137600), ([3,7,9], 82087680), ([3,7,10], 64683600), ([3,7,11], 87060960), ([3,7,12], 89438640), ([3,7,13], 105904560), ([3,7,14], 122426640), ([3,8,8], 36201600), ([3,8,9], 99174240), ([3,8,10], 78505200), ([3,8,11], 104116320), ([3,8,12], 105652080), ([3,8,13], 109812240), ([3,8,14], 153509040), ([3,9,9], 74908800), ([3,9,10], 124263720), ([3,9,11], 176277600), ([3,9,12], 180672120), ([3,9,13], 113707800), ([3,9,14], 182823480), ([3,10,10], 57262464), ([3,10,11], 145208160), ([3,10,12], 171628740), ([3,10,13], 121886640), ([3,10,14], 154082790), ([3,11,11], 98175240), ([3,11,12], 171553680), ([3,11,13], 120222360), ([3,11,14], 170511480), ([3,12,12], 64707660), ([3,12,13], 94666860), ([3,12,14], 155708190), ([3,13,13], 15264720), ([3,13,14], 99311130), ([3,14,14], 79701570), ([4,4,4], 2931840), ([4,4,9], 19845360), ([4,4,11], 221760), ([4,5,7], 1900800), ([4,5,8], 3801600), ([4,5,9], 33785280), ([4,5,10], 4849920), ([4,5,11], 11026080), ([4,5,12], 22376160), ([4,5,13], 37272960), ([4,5,14], 54092880), ([4,6,6], 5466240), ([4,6,7], 13541760), ([4,6,8], 16151040), ([4,6,9], 42252480), ([4,6,10], 23506560), ([4,6,11], 33835680), ([4,6,12], 49206240), ([4,6,13], 68711040), ([4,6,14], 89836560), ([4,7,7], 14188800), ([4,7,8], 30462720), ([4,7,9], 52680000), ([4,7,10], 40726320), ([4,7,11], 56645280), ([4,7,12], 70185840), ([4,7,13], 91753680), ([4,7,14], 114639840), ([4,8,8], 24301440), ([4,8,9], 70267680), ([4,8,10], 57675600), ([4,8,11], 79454880), ([4,8,12], 94062960), ([4,8,13], 105234480), ([4,8,14], 156846240), ([4,9,9], 59616000), ([4,9,10], 103584600)]
theorem block005_data : block005 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35700480 : Int) atom0393) (SparsePolynomial.scale (72161280 : Int) atom0394)) (SparsePolynomial.merge (SparsePolynomial.scale (50591520 : Int) atom0395) (SparsePolynomial.merge (SparsePolynomial.scale (70005600 : Int) atom0396) (SparsePolynomial.scale (76122720 : Int) atom0397)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (92435040 : Int) atom0398) (SparsePolynomial.scale (108747360 : Int) atom0399)) (SparsePolynomial.merge (SparsePolynomial.scale (25864320 : Int) atom0400) (SparsePolynomial.merge (SparsePolynomial.scale (52137600 : Int) atom0401) (SparsePolynomial.scale (82087680 : Int) atom0402))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64683600 : Int) atom0403) (SparsePolynomial.scale (87060960 : Int) atom0404)) (SparsePolynomial.merge (SparsePolynomial.scale (89438640 : Int) atom0405) (SparsePolynomial.merge (SparsePolynomial.scale (105904560 : Int) atom0406) (SparsePolynomial.scale (122426640 : Int) atom0407)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36201600 : Int) atom0408) (SparsePolynomial.scale (99174240 : Int) atom0409)) (SparsePolynomial.merge (SparsePolynomial.scale (78505200 : Int) atom0410) (SparsePolynomial.merge (SparsePolynomial.scale (104116320 : Int) atom0411) (SparsePolynomial.scale (105652080 : Int) atom0412)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (109812240 : Int) atom0413) (SparsePolynomial.scale (153509040 : Int) atom0414)) (SparsePolynomial.merge (SparsePolynomial.scale (74908800 : Int) atom0415) (SparsePolynomial.merge (SparsePolynomial.scale (124263720 : Int) atom0416) (SparsePolynomial.scale (176277600 : Int) atom0417)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (180672120 : Int) atom0418) (SparsePolynomial.scale (113707800 : Int) atom0419)) (SparsePolynomial.merge (SparsePolynomial.scale (182823480 : Int) atom0420) (SparsePolynomial.merge (SparsePolynomial.scale (57262464 : Int) atom0421) (SparsePolynomial.scale (145208160 : Int) atom0422))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (171628740 : Int) atom0423) (SparsePolynomial.scale (121886640 : Int) atom0424)) (SparsePolynomial.merge (SparsePolynomial.scale (154082790 : Int) atom0425) (SparsePolynomial.merge (SparsePolynomial.scale (98175240 : Int) atom0426) (SparsePolynomial.scale (171553680 : Int) atom0427)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (120222360 : Int) atom0428) (SparsePolynomial.scale (170511480 : Int) atom0429)) (SparsePolynomial.merge (SparsePolynomial.scale (64707660 : Int) atom0430) (SparsePolynomial.merge (SparsePolynomial.scale (94666860 : Int) atom0431) (SparsePolynomial.scale (155708190 : Int) atom0432))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15264720 : Int) atom0433) (SparsePolynomial.scale (99311130 : Int) atom0434)) (SparsePolynomial.merge (SparsePolynomial.scale (79701570 : Int) atom0435) (SparsePolynomial.merge (SparsePolynomial.scale (2931840 : Int) atom0436) (SparsePolynomial.scale (19845360 : Int) atom0437)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (221760 : Int) atom0438) (SparsePolynomial.scale (1900800 : Int) atom0439)) (SparsePolynomial.merge (SparsePolynomial.scale (3801600 : Int) atom0440) (SparsePolynomial.merge (SparsePolynomial.scale (33785280 : Int) atom0441) (SparsePolynomial.scale (4849920 : Int) atom0442))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11026080 : Int) atom0443) (SparsePolynomial.scale (22376160 : Int) atom0444)) (SparsePolynomial.merge (SparsePolynomial.scale (37272960 : Int) atom0445) (SparsePolynomial.merge (SparsePolynomial.scale (54092880 : Int) atom0446) (SparsePolynomial.scale (5466240 : Int) atom0447)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13541760 : Int) atom0448) (SparsePolynomial.scale (16151040 : Int) atom0449)) (SparsePolynomial.merge (SparsePolynomial.scale (42252480 : Int) atom0450) (SparsePolynomial.merge (SparsePolynomial.scale (23506560 : Int) atom0451) (SparsePolynomial.scale (33835680 : Int) atom0452)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49206240 : Int) atom0453) (SparsePolynomial.scale (68711040 : Int) atom0454)) (SparsePolynomial.merge (SparsePolynomial.scale (89836560 : Int) atom0455) (SparsePolynomial.merge (SparsePolynomial.scale (14188800 : Int) atom0456) (SparsePolynomial.scale (30462720 : Int) atom0457)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52680000 : Int) atom0458) (SparsePolynomial.scale (40726320 : Int) atom0459)) (SparsePolynomial.merge (SparsePolynomial.scale (56645280 : Int) atom0460) (SparsePolynomial.merge (SparsePolynomial.scale (70185840 : Int) atom0461) (SparsePolynomial.scale (91753680 : Int) atom0462))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (114639840 : Int) atom0463) (SparsePolynomial.scale (24301440 : Int) atom0464)) (SparsePolynomial.merge (SparsePolynomial.scale (70267680 : Int) atom0465) (SparsePolynomial.merge (SparsePolynomial.scale (57675600 : Int) atom0466) (SparsePolynomial.scale (79454880 : Int) atom0467)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (94062960 : Int) atom0468) (SparsePolynomial.scale (105234480 : Int) atom0469)) (SparsePolynomial.merge (SparsePolynomial.scale (156846240 : Int) atom0470) (SparsePolynomial.merge (SparsePolynomial.scale (59616000 : Int) atom0471) (SparsePolynomial.scale (103584600 : Int) atom0472)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block005 := by
  rw [block005_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0393_nonneg g hg hA hB) (atom0394_nonneg g hg hA hB)) (add_nonneg (atom0395_nonneg g hg hA hB) (add_nonneg (atom0396_nonneg g hg hA hB) (atom0397_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0398_nonneg g hg hA hB) (atom0399_nonneg g hg hA hB)) (add_nonneg (atom0400_nonneg g hg hA hB) (add_nonneg (atom0401_nonneg g hg hA hB) (atom0402_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0403_nonneg g hg hA hB) (atom0404_nonneg g hg hA hB)) (add_nonneg (atom0405_nonneg g hg hA hB) (add_nonneg (atom0406_nonneg g hg hA hB) (atom0407_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0408_nonneg g hg hA hB) (atom0409_nonneg g hg hA hB)) (add_nonneg (atom0410_nonneg g hg hA hB) (add_nonneg (atom0411_nonneg g hg hA hB) (atom0412_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0413_nonneg g hg hA hB) (atom0414_nonneg g hg hA hB)) (add_nonneg (atom0415_nonneg g hg hA hB) (add_nonneg (atom0416_nonneg g hg hA hB) (atom0417_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0418_nonneg g hg hA hB) (atom0419_nonneg g hg hA hB)) (add_nonneg (atom0420_nonneg g hg hA hB) (add_nonneg (atom0421_nonneg g hg hA hB) (atom0422_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0423_nonneg g hg hA hB) (atom0424_nonneg g hg hA hB)) (add_nonneg (atom0425_nonneg g hg hA hB) (add_nonneg (atom0426_nonneg g hg hA hB) (atom0427_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0428_nonneg g hg hA hB) (atom0429_nonneg g hg hA hB)) (add_nonneg (atom0430_nonneg g hg hA hB) (add_nonneg (atom0431_nonneg g hg hA hB) (atom0432_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0433_nonneg g hg hA hB) (atom0434_nonneg g hg hA hB)) (add_nonneg (atom0435_nonneg g hg hA hB) (add_nonneg (atom0436_nonneg g hg hA hB) (atom0437_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0438_nonneg g hg hA hB) (atom0439_nonneg g hg hA hB)) (add_nonneg (atom0440_nonneg g hg hA hB) (add_nonneg (atom0441_nonneg g hg hA hB) (atom0442_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0443_nonneg g hg hA hB) (atom0444_nonneg g hg hA hB)) (add_nonneg (atom0445_nonneg g hg hA hB) (add_nonneg (atom0446_nonneg g hg hA hB) (atom0447_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0448_nonneg g hg hA hB) (atom0449_nonneg g hg hA hB)) (add_nonneg (atom0450_nonneg g hg hA hB) (add_nonneg (atom0451_nonneg g hg hA hB) (atom0452_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0453_nonneg g hg hA hB) (atom0454_nonneg g hg hA hB)) (add_nonneg (atom0455_nonneg g hg hA hB) (add_nonneg (atom0456_nonneg g hg hA hB) (atom0457_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0458_nonneg g hg hA hB) (atom0459_nonneg g hg hA hB)) (add_nonneg (atom0460_nonneg g hg hA hB) (add_nonneg (atom0461_nonneg g hg hA hB) (atom0462_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0463_nonneg g hg hA hB) (atom0464_nonneg g hg hA hB)) (add_nonneg (atom0465_nonneg g hg hA hB) (add_nonneg (atom0466_nonneg g hg hA hB) (atom0467_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0468_nonneg g hg hA hB) (atom0469_nonneg g hg hA hB)) (add_nonneg (atom0470_nonneg g hg hA hB) (add_nonneg (atom0471_nonneg g hg hA hB) (atom0472_nonneg g hg hA hB))))))))

end APPT.Finite15
