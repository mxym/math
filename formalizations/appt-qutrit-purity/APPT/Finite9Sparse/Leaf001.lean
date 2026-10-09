import APPT.Finite9Sparse.Base00
import APPT.Finite9Sparse.Base01
import APPT.Finite9Sparse.Base02
import APPT.Finite9Sparse.Base03
import APPT.Finite9Sparse.Base04
import APPT.Finite9Sparse.Base05
import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0080 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0080 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (297000 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0081 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (922320 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0082 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262368 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0083 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (692820 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0084 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1045440 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0085 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (635040 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0086 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924480 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0087 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (500580 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0088 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (997380 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0089 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (775440 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0090 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1195560 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0091 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (421200 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0092 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854820 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0093 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1395360 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0094 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347760 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0095 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1351350 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0096 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (933120 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0097 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161280 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0098 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370080 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0099 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (525240 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0100 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (609120 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0101 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28800 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0102 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (381600 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0103 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283032 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0104 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (867060 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0105 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1316160 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0106 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (535680 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0107 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (921600 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0108 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (610740 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0109 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1350900 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0110 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (816120 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0111 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (811080 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0112 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (639360 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0113 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1025280 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0114 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (771840 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0115 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (518400 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0116 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (930240 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0117 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311040 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0118 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom0119 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121716 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0120 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425304 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom0121 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127080 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0122 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (295416 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0123 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353160 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0124 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1103400 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([4,5,7], 1)]
theorem eval_atom0125 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (836280 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([4,5,8], 1)]
theorem eval_atom0126 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (964440 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0127 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (624240 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0128 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1164960 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0129 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1081440 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0130 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (648000 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0131 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1396080 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0132 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (622080 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom0133 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121500 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom0134 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (495180 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom0135 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428220 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom0136 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289980 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom0137 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (609120 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([5,6,7], 1)]
theorem eval_atom0138 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1304640 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([5,6,8], 1)]
theorem eval_atom0139 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853200 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom0140 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (777600 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([5,7,8], 1)]
theorem eval_atom0141 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1324080 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom0142 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (395280 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom0143 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198000 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom0144 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (722160 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom0145 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (383760 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom0146 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (907200 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([6,7,8], 1)]
theorem eval_atom0147 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1394640 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom0148 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311040 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom0149 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345600 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom0150 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (930240 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom0151 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (622080 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -4), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -8), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -6), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -10), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -4), ([1,5,6], -8), ([1,5,7], -4), ([1,5,8], -4), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -4), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -10), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -4), ([2,5,6], -8), ([2,5,7], -4), ([2,5,8], -4), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -8), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -14), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -6), ([3,5,6], -12), ([3,5,7], -4), ([3,5,8], -4), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -6), ([4,5,6], -12), ([4,5,7], -4), ([4,5,8], -4), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -2), ([5,5,6], -6), ([5,5,7], -2), ([5,5,8], -2), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 4), ([5,7,8], 8), ([5,8,8], 8), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [] 1 base00 := by decide +kernel
theorem eval_atom0152 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = (detA (outer g)) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49410 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (detA (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153 : SparsePolynomial.Poly := [([0,1,4], -4), ([1,1,4], -12), ([1,2,4], -16), ([1,3,4], -8), ([1,4,4], -4), ([1,4,5], 4), ([1,4,6], 6), ([1,4,7], 10), ([1,4,8], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [1,4] 1 base01 := by decide +kernel
theorem eval_atom0153 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = (quadA (outer g) ![2,1,2] * g 1 * g 4) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6575 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([0,1,7], -4), ([1,1,7], -12), ([1,2,7], -16), ([1,3,7], -8), ([1,4,7], -4), ([1,5,7], 4), ([1,6,7], 6), ([1,7,7], 10), ([1,7,8], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [1,7] 1 base01 := by decide +kernel
theorem eval_atom0154 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = (quadA (outer g) ![2,1,2] * g 1 * g 7) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8005 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([0,1,8], -4), ([1,1,8], -12), ([1,2,8], -16), ([1,3,8], -8), ([1,4,8], -4), ([1,5,8], 4), ([1,6,8], 6), ([1,7,8], 10), ([1,8,8], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [1,8] 1 base01 := by decide +kernel
theorem eval_atom0155 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = (quadA (outer g) ![2,1,2] * g 1 * g 8) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15915 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -14), ([1,1,4], -10), ([1,1,5], -6), ([1,1,6], 2), ([1,1,7], 10), ([1,1,8], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [1,1] 1 base02 := by decide +kernel
theorem eval_atom0156 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = (quadA (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10470 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -6), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -10), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -4), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -12), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -16), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -12), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -8), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -8), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -8), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -20), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -16), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -10), ([2,5,6], -14), ([2,5,7], -8), ([2,5,8], -8), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -12), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -20), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -12), ([3,5,6], -18), ([3,5,7], -8), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -8), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -10), ([4,5,6], -16), ([4,5,7], -8), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -4), ([5,5,6], -8), ([5,5,7], -4), ([5,5,8], 4), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 12), ([5,7,8], 16), ([5,8,8], 16), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem atom0157_data : atom0157 = SparsePolynomial.monoTimes [] 1 base03 := by decide +kernel
theorem eval_atom0157 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = (detB (outer g)) := by
  rw [atom0157_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67230 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (detB (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,8], 4), ([0,6,6], -1), ([0,6,8], 4), ([0,7,8], 4), ([0,8,8], 4)]
theorem atom0158_data : atom0158 = SparsePolynomial.monoTimes [0] 1 base04 := by decide +kernel
theorem eval_atom0158 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0158_data, SparsePolynomial.eval_monoTimes, eval_base04]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37440 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base04_nonneg g hg hA hB
  rw [eval_base04] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([0,0,8], -2), ([0,1,8], -2), ([0,2,8], -2), ([0,3,8], -2), ([0,4,8], -2), ([0,7,8], 2), ([0,8,8], 4)]
theorem atom0159_data : atom0159 = SparsePolynomial.monoTimes [0,8] 1 base05 := by decide +kernel
theorem eval_atom0159 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = (quadB (outer g) ![1,1,0] * g 0 * g 8) := by
  rw [atom0159_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40320 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def block001 : SparsePolynomial.Poly := [([0,0,0], -37440), ([0,0,1], -74880), ([0,0,2], -74880), ([0,0,3], -308160), ([0,0,4], -308160), ([0,0,5], -308160), ([0,0,6], -308160), ([0,0,7], -233280), ([0,0,8], -313920), ([0,1,1], -121200), ([0,1,2], -308160), ([0,1,3], -774720), ([0,1,4], -567740), ([0,1,5], -541440), ([0,1,6], -541440), ([0,1,7], -498580), ([0,1,8], -610860), ([0,2,2], -270720), ([0,2,3], -1008000), ([0,2,4], -774720), ([0,2,5], -675900), ([0,2,6], -541440), ([0,2,7], -466560), ([0,2,8], -547200), ([0,3,3], -737280), ([0,3,4], -1241280), ([0,3,5], -1142460), ([0,3,6], -1008000), ([0,3,7], -466560), ([0,3,8], -547200), ([0,4,4], -504000), ([0,4,5], -1008000), ([0,4,6], -1008000), ([0,4,7], -466560), ([0,4,8], -547200), ([0,5,5], -504000), ([0,5,6], -1008000), ([0,5,7], -466560), ([0,5,8], -316800), ([0,6,6], -504000), ([0,6,7], -466560), ([0,6,8], -316800), ([0,7,8], 230400), ([0,8,8], 311040), ([1,1,1], -125640), ([1,1,2], -400800), ([1,1,3], -613140), ([1,1,4], -416880), ([1,1,5], -430560), ([1,1,6], -445620), ([1,1,7], -457920), ([1,1,8], -469080), ([1,2,2], -466560), ([1,2,3], -1399680), ([1,2,4], -1038320), ([1,2,5], -1103220), ([1,2,6], -1166400), ([1,2,7], -1061200), ([1,2,8], -1187760), ([1,3,3], -933120), ([1,3,4], -1452280), ([1,3,5], -1569780), ([1,3,6], -1632960), ([1,3,7], -997160), ([1,3,8], -1060440), ([1,4,4], -492860), ([1,4,5], -1175740), ([1,4,6], -1360230), ([1,4,7], -899390), ([1,4,8], -878430), ([1,5,5], -735480), ([1,5,6], -1202040), ([1,5,7], -703460), ([1,5,8], -671820), ([1,6,6], -466560), ([1,6,7], -418530), ([1,6,8], -371070), ([1,7,7], 80050), ([1,7,8], 303240), ([1,8,8], 286470), ([2,2,2], -233280), ([2,2,3], -933120), ([2,2,4], -699840), ([2,2,5], -735480), ([2,2,6], -699840), ([2,2,7], -466560), ([2,2,8], -699840), ([2,3,3], -1166400), ([2,3,4], -1866240), ([2,3,5], -1937520), ([2,3,6], -1866240), ([2,3,7], -636120), ([2,3,8], -477360), ([2,4,4], -437472), ([2,4,5], -876960), ([2,4,6], -587520), ([2,4,7], -298080), ([2,4,8], -8640), ([2,5,5], -369360), ([2,5,6], -339120), ([2,5,7], 39960), ([2,5,8], 460080), ([2,6,6], -45360), ([2,6,7], 388260), ([2,6,8], 928800), ([2,7,7], 347760), ([2,7,8], 1351350), ([2,8,8], 933120), ([3,3,3], -305280), ([3,3,4], -796320), ([3,3,5], -676800), ([3,3,6], -557280), ([3,3,7], -437760), ([3,3,8], -318240), ([3,4,4], -650088), ([3,4,5], -1169280), ([3,4,6], -783360), ([3,4,7], -397440), ([3,4,8], -11520), ([3,5,5], -492480), ([3,5,6], -452160), ([3,5,7], 80640), ([3,5,8], 613440), ([3,6,6], -60480), ([3,6,7], 558720), ([3,6,8], 1238400), ([3,7,7], 518400), ([3,7,8], 1863360), ([3,8,8], 1244160), ([4,4,4], -232920), ([4,4,5], -712584), ([4,4,6], -507816), ([4,4,7], -339480), ([4,4,8], -171144), ([4,5,5], -615600), ([4,5,6], -565200), ([4,5,7], 100800), ([4,5,8], 766800), ([4,6,6], -75600), ([4,6,7], 698400), ([4,6,8], 1548000), ([4,7,7], 648000), ([4,7,8], 2329200), ([4,8,8], 1555200), ([5,5,5], -246240), ([5,5,6], -339120), ([5,5,7], 60480), ([5,5,8], 460080), ([5,6,6], -90720), ([5,6,7], 838080), ([5,6,8], 1857600), ([5,7,7], 777600), ([5,7,8], 2795040), ([5,8,8], 1866240), ([6,6,6], -35280), ([6,6,7], 488880), ([6,6,8], 1083600), ([6,7,7], 907200), ([6,7,8], 3260880), ([6,8,8], 2177280), ([7,7,7], 345600), ([7,7,8], 1863360), ([7,8,8], 2488320), ([8,8,8], 933120)]
theorem block001_data : block001 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (297000 : Int) atom0080) (SparsePolynomial.scale (922320 : Int) atom0081)) (SparsePolynomial.merge (SparsePolynomial.scale (262368 : Int) atom0082) (SparsePolynomial.merge (SparsePolynomial.scale (692820 : Int) atom0083) (SparsePolynomial.scale (1045440 : Int) atom0084)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (635040 : Int) atom0085) (SparsePolynomial.scale (924480 : Int) atom0086)) (SparsePolynomial.merge (SparsePolynomial.scale (500580 : Int) atom0087) (SparsePolynomial.merge (SparsePolynomial.scale (997380 : Int) atom0088) (SparsePolynomial.scale (775440 : Int) atom0089))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1195560 : Int) atom0090) (SparsePolynomial.scale (421200 : Int) atom0091)) (SparsePolynomial.merge (SparsePolynomial.scale (854820 : Int) atom0092) (SparsePolynomial.merge (SparsePolynomial.scale (1395360 : Int) atom0093) (SparsePolynomial.scale (347760 : Int) atom0094)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1351350 : Int) atom0095) (SparsePolynomial.scale (933120 : Int) atom0096)) (SparsePolynomial.merge (SparsePolynomial.scale (161280 : Int) atom0097) (SparsePolynomial.merge (SparsePolynomial.scale (370080 : Int) atom0098) (SparsePolynomial.scale (525240 : Int) atom0099)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (609120 : Int) atom0100) (SparsePolynomial.scale (28800 : Int) atom0101)) (SparsePolynomial.merge (SparsePolynomial.scale (381600 : Int) atom0102) (SparsePolynomial.merge (SparsePolynomial.scale (283032 : Int) atom0103) (SparsePolynomial.scale (867060 : Int) atom0104)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1316160 : Int) atom0105) (SparsePolynomial.scale (535680 : Int) atom0106)) (SparsePolynomial.merge (SparsePolynomial.scale (921600 : Int) atom0107) (SparsePolynomial.merge (SparsePolynomial.scale (610740 : Int) atom0108) (SparsePolynomial.scale (1350900 : Int) atom0109))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (816120 : Int) atom0110) (SparsePolynomial.scale (811080 : Int) atom0111)) (SparsePolynomial.merge (SparsePolynomial.scale (639360 : Int) atom0112) (SparsePolynomial.merge (SparsePolynomial.scale (1025280 : Int) atom0113) (SparsePolynomial.scale (771840 : Int) atom0114)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (518400 : Int) atom0115) (SparsePolynomial.scale (930240 : Int) atom0116)) (SparsePolynomial.merge (SparsePolynomial.scale (311040 : Int) atom0117) (SparsePolynomial.merge (SparsePolynomial.scale (360 : Int) atom0118) (SparsePolynomial.scale (121716 : Int) atom0119))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (425304 : Int) atom0120) (SparsePolynomial.scale (127080 : Int) atom0121)) (SparsePolynomial.merge (SparsePolynomial.scale (295416 : Int) atom0122) (SparsePolynomial.merge (SparsePolynomial.scale (353160 : Int) atom0123) (SparsePolynomial.scale (1103400 : Int) atom0124)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (836280 : Int) atom0125) (SparsePolynomial.scale (964440 : Int) atom0126)) (SparsePolynomial.merge (SparsePolynomial.scale (624240 : Int) atom0127) (SparsePolynomial.merge (SparsePolynomial.scale (1164960 : Int) atom0128) (SparsePolynomial.scale (1081440 : Int) atom0129))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (648000 : Int) atom0130) (SparsePolynomial.scale (1396080 : Int) atom0131)) (SparsePolynomial.merge (SparsePolynomial.scale (622080 : Int) atom0132) (SparsePolynomial.merge (SparsePolynomial.scale (121500 : Int) atom0133) (SparsePolynomial.scale (495180 : Int) atom0134)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (428220 : Int) atom0135) (SparsePolynomial.scale (289980 : Int) atom0136)) (SparsePolynomial.merge (SparsePolynomial.scale (609120 : Int) atom0137) (SparsePolynomial.merge (SparsePolynomial.scale (1304640 : Int) atom0138) (SparsePolynomial.scale (853200 : Int) atom0139)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (777600 : Int) atom0140) (SparsePolynomial.scale (1324080 : Int) atom0141)) (SparsePolynomial.merge (SparsePolynomial.scale (395280 : Int) atom0142) (SparsePolynomial.merge (SparsePolynomial.scale (198000 : Int) atom0143) (SparsePolynomial.scale (722160 : Int) atom0144)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (383760 : Int) atom0145) (SparsePolynomial.scale (907200 : Int) atom0146)) (SparsePolynomial.merge (SparsePolynomial.scale (1394640 : Int) atom0147) (SparsePolynomial.merge (SparsePolynomial.scale (311040 : Int) atom0148) (SparsePolynomial.scale (345600 : Int) atom0149))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (930240 : Int) atom0150) (SparsePolynomial.scale (622080 : Int) atom0151)) (SparsePolynomial.merge (SparsePolynomial.scale (49410 : Int) atom0152) (SparsePolynomial.merge (SparsePolynomial.scale (6575 : Int) atom0153) (SparsePolynomial.scale (8005 : Int) atom0154)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15915 : Int) atom0155) (SparsePolynomial.scale (10470 : Int) atom0156)) (SparsePolynomial.merge (SparsePolynomial.scale (67230 : Int) atom0157) (SparsePolynomial.merge (SparsePolynomial.scale (37440 : Int) atom0158) (SparsePolynomial.scale (40320 : Int) atom0159)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block001 := by
  rw [block001_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0080_nonneg g hg hA hB) (atom0081_nonneg g hg hA hB)) (add_nonneg (atom0082_nonneg g hg hA hB) (add_nonneg (atom0083_nonneg g hg hA hB) (atom0084_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0085_nonneg g hg hA hB) (atom0086_nonneg g hg hA hB)) (add_nonneg (atom0087_nonneg g hg hA hB) (add_nonneg (atom0088_nonneg g hg hA hB) (atom0089_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0090_nonneg g hg hA hB) (atom0091_nonneg g hg hA hB)) (add_nonneg (atom0092_nonneg g hg hA hB) (add_nonneg (atom0093_nonneg g hg hA hB) (atom0094_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0095_nonneg g hg hA hB) (atom0096_nonneg g hg hA hB)) (add_nonneg (atom0097_nonneg g hg hA hB) (add_nonneg (atom0098_nonneg g hg hA hB) (atom0099_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0100_nonneg g hg hA hB) (atom0101_nonneg g hg hA hB)) (add_nonneg (atom0102_nonneg g hg hA hB) (add_nonneg (atom0103_nonneg g hg hA hB) (atom0104_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0105_nonneg g hg hA hB) (atom0106_nonneg g hg hA hB)) (add_nonneg (atom0107_nonneg g hg hA hB) (add_nonneg (atom0108_nonneg g hg hA hB) (atom0109_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0110_nonneg g hg hA hB) (atom0111_nonneg g hg hA hB)) (add_nonneg (atom0112_nonneg g hg hA hB) (add_nonneg (atom0113_nonneg g hg hA hB) (atom0114_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0115_nonneg g hg hA hB) (atom0116_nonneg g hg hA hB)) (add_nonneg (atom0117_nonneg g hg hA hB) (add_nonneg (atom0118_nonneg g hg hA hB) (atom0119_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0120_nonneg g hg hA hB) (atom0121_nonneg g hg hA hB)) (add_nonneg (atom0122_nonneg g hg hA hB) (add_nonneg (atom0123_nonneg g hg hA hB) (atom0124_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0125_nonneg g hg hA hB) (atom0126_nonneg g hg hA hB)) (add_nonneg (atom0127_nonneg g hg hA hB) (add_nonneg (atom0128_nonneg g hg hA hB) (atom0129_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0130_nonneg g hg hA hB) (atom0131_nonneg g hg hA hB)) (add_nonneg (atom0132_nonneg g hg hA hB) (add_nonneg (atom0133_nonneg g hg hA hB) (atom0134_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0135_nonneg g hg hA hB) (atom0136_nonneg g hg hA hB)) (add_nonneg (atom0137_nonneg g hg hA hB) (add_nonneg (atom0138_nonneg g hg hA hB) (atom0139_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0140_nonneg g hg hA hB) (atom0141_nonneg g hg hA hB)) (add_nonneg (atom0142_nonneg g hg hA hB) (add_nonneg (atom0143_nonneg g hg hA hB) (atom0144_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0145_nonneg g hg hA hB) (atom0146_nonneg g hg hA hB)) (add_nonneg (atom0147_nonneg g hg hA hB) (add_nonneg (atom0148_nonneg g hg hA hB) (atom0149_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0150_nonneg g hg hA hB) (atom0151_nonneg g hg hA hB)) (add_nonneg (atom0152_nonneg g hg hA hB) (add_nonneg (atom0153_nonneg g hg hA hB) (atom0154_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0155_nonneg g hg hA hB) (atom0156_nonneg g hg hA hB)) (add_nonneg (atom0157_nonneg g hg hA hB) (add_nonneg (atom0158_nonneg g hg hA hB) (atom0159_nonneg g hg hA hB))))))))

end APPT.Finite9
