import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0080 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0080 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62752 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0081 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17568 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0082 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24768 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0083 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28928 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0084 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107136 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0085 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57088 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0086 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76416 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0087 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82560 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0088 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84440 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0089 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89344 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0090 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21888 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0091 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39008 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0092 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109824 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0093 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69952 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0094 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90624 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095 : SparsePolynomial.Poly := [([1,4,9], 1)]
theorem eval_atom0095 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102528 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096 : SparsePolynomial.Poly := [([1,4,10], 1)]
theorem eval_atom0096 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109856 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([1,4,11], 1)]
theorem eval_atom0097 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120832 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0098 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33152 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0099 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113536 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0100 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83712 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0101 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104320 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([1,5,9], 1)]
theorem eval_atom0102 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121728 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([1,5,10], 1)]
theorem eval_atom0103 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127200 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([1,5,11], 1)]
theorem eval_atom0104 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150016 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0105 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95616 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0106 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147584 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0107 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195072 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([1,6,9], 1)]
theorem eval_atom0108 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218112 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([1,6,10], 1)]
theorem eval_atom0109 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134656 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([1,6,11], 1)]
theorem eval_atom0110 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168824 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0111 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60736 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0112 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140864 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([1,7,9], 1)]
theorem eval_atom0113 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191712 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([1,7,10], 1)]
theorem eval_atom0114 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142048 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([1,7,11], 1)]
theorem eval_atom0115 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166552 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0116 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105216 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([1,8,9], 1)]
theorem eval_atom0117 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193344 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([1,8,10], 1)]
theorem eval_atom0118 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145792 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([1,8,11], 1)]
theorem eval_atom0119 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177848 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([1,9,9], 1)]
theorem eval_atom0120 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81504 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([1,9,10], 1)]
theorem eval_atom0121 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118752 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([1,9,11], 1)]
theorem eval_atom0122 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152720 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([1,10,10], 1)]
theorem eval_atom0123 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26176 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([1,10,11], 1)]
theorem eval_atom0124 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76064 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([1,11,11], 1)]
theorem eval_atom0125 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34272 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0126 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8640 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0127 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24768 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0128 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23616 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0129 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22464 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0130 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59328 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([2,2,7], 1)]
theorem eval_atom0131 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20160 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0132 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30912 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([2,2,9], 1)]
theorem eval_atom0133 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17856 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([2,2,11], 1)]
theorem eval_atom0134 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22080 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0135 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24960 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0136 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38208 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0137 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40320 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0138 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122688 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0139 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52992 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0140 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83136 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([2,3,9], 1)]
theorem eval_atom0141 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65664 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([2,3,10], 1)]
theorem eval_atom0142 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52272 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([2,3,11], 1)]
theorem eval_atom0143 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84864 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0144 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30336 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0145 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62016 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0146 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126720 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0147 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74496 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0148 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104448 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([2,4,9], 1)]
theorem eval_atom0149 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95616 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([2,4,10], 1)]
theorem eval_atom0150 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90240 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([2,4,11], 1)]
theorem eval_atom0151 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132096 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0152 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43200 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0153 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130752 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0154 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96768 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0155 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125760 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([2,5,9], 1)]
theorem eval_atom0156 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125568 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([2,5,10], 1)]
theorem eval_atom0157 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114624 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([2,5,11], 1)]
theorem eval_atom0158 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179328 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0159 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105408 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block001 : SparsePolynomial.Poly := [([1,2,11], 62752), ([1,3,3], 17568), ([1,3,4], 24768), ([1,3,5], 28928), ([1,3,6], 107136), ([1,3,7], 57088), ([1,3,8], 76416), ([1,3,9], 82560), ([1,3,10], 84440), ([1,3,11], 89344), ([1,4,4], 21888), ([1,4,5], 39008), ([1,4,6], 109824), ([1,4,7], 69952), ([1,4,8], 90624), ([1,4,9], 102528), ([1,4,10], 109856), ([1,4,11], 120832), ([1,5,5], 33152), ([1,5,6], 113536), ([1,5,7], 83712), ([1,5,8], 104320), ([1,5,9], 121728), ([1,5,10], 127200), ([1,5,11], 150016), ([1,6,6], 95616), ([1,6,7], 147584), ([1,6,8], 195072), ([1,6,9], 218112), ([1,6,10], 134656), ([1,6,11], 168824), ([1,7,7], 60736), ([1,7,8], 140864), ([1,7,9], 191712), ([1,7,10], 142048), ([1,7,11], 166552), ([1,8,8], 105216), ([1,8,9], 193344), ([1,8,10], 145792), ([1,8,11], 177848), ([1,9,9], 81504), ([1,9,10], 118752), ([1,9,11], 152720), ([1,10,10], 26176), ([1,10,11], 76064), ([1,11,11], 34272), ([2,2,2], 8640), ([2,2,3], 24768), ([2,2,4], 23616), ([2,2,5], 22464), ([2,2,6], 59328), ([2,2,7], 20160), ([2,2,8], 30912), ([2,2,9], 17856), ([2,2,11], 22080), ([2,3,3], 24960), ([2,3,4], 38208), ([2,3,5], 40320), ([2,3,6], 122688), ([2,3,7], 52992), ([2,3,8], 83136), ([2,3,9], 65664), ([2,3,10], 52272), ([2,3,11], 84864), ([2,4,4], 30336), ([2,4,5], 62016), ([2,4,6], 126720), ([2,4,7], 74496), ([2,4,8], 104448), ([2,4,9], 95616), ([2,4,10], 90240), ([2,4,11], 132096), ([2,5,5], 43200), ([2,5,6], 130752), ([2,5,7], 96768), ([2,5,8], 125760), ([2,5,9], 125568), ([2,5,10], 114624), ([2,5,11], 179328), ([2,6,6], 105408)]
theorem block001_data : block001 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62752 : Int) atom0080) (SparsePolynomial.scale (17568 : Int) atom0081)) (SparsePolynomial.merge (SparsePolynomial.scale (24768 : Int) atom0082) (SparsePolynomial.merge (SparsePolynomial.scale (28928 : Int) atom0083) (SparsePolynomial.scale (107136 : Int) atom0084)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (57088 : Int) atom0085) (SparsePolynomial.scale (76416 : Int) atom0086)) (SparsePolynomial.merge (SparsePolynomial.scale (82560 : Int) atom0087) (SparsePolynomial.merge (SparsePolynomial.scale (84440 : Int) atom0088) (SparsePolynomial.scale (89344 : Int) atom0089))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21888 : Int) atom0090) (SparsePolynomial.scale (39008 : Int) atom0091)) (SparsePolynomial.merge (SparsePolynomial.scale (109824 : Int) atom0092) (SparsePolynomial.merge (SparsePolynomial.scale (69952 : Int) atom0093) (SparsePolynomial.scale (90624 : Int) atom0094)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (102528 : Int) atom0095) (SparsePolynomial.scale (109856 : Int) atom0096)) (SparsePolynomial.merge (SparsePolynomial.scale (120832 : Int) atom0097) (SparsePolynomial.merge (SparsePolynomial.scale (33152 : Int) atom0098) (SparsePolynomial.scale (113536 : Int) atom0099)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (83712 : Int) atom0100) (SparsePolynomial.scale (104320 : Int) atom0101)) (SparsePolynomial.merge (SparsePolynomial.scale (121728 : Int) atom0102) (SparsePolynomial.merge (SparsePolynomial.scale (127200 : Int) atom0103) (SparsePolynomial.scale (150016 : Int) atom0104)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (95616 : Int) atom0105) (SparsePolynomial.scale (147584 : Int) atom0106)) (SparsePolynomial.merge (SparsePolynomial.scale (195072 : Int) atom0107) (SparsePolynomial.merge (SparsePolynomial.scale (218112 : Int) atom0108) (SparsePolynomial.scale (134656 : Int) atom0109))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (168824 : Int) atom0110) (SparsePolynomial.scale (60736 : Int) atom0111)) (SparsePolynomial.merge (SparsePolynomial.scale (140864 : Int) atom0112) (SparsePolynomial.merge (SparsePolynomial.scale (191712 : Int) atom0113) (SparsePolynomial.scale (142048 : Int) atom0114)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (166552 : Int) atom0115) (SparsePolynomial.scale (105216 : Int) atom0116)) (SparsePolynomial.merge (SparsePolynomial.scale (193344 : Int) atom0117) (SparsePolynomial.merge (SparsePolynomial.scale (145792 : Int) atom0118) (SparsePolynomial.scale (177848 : Int) atom0119))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (81504 : Int) atom0120) (SparsePolynomial.scale (118752 : Int) atom0121)) (SparsePolynomial.merge (SparsePolynomial.scale (152720 : Int) atom0122) (SparsePolynomial.merge (SparsePolynomial.scale (26176 : Int) atom0123) (SparsePolynomial.scale (76064 : Int) atom0124)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34272 : Int) atom0125) (SparsePolynomial.scale (8640 : Int) atom0126)) (SparsePolynomial.merge (SparsePolynomial.scale (24768 : Int) atom0127) (SparsePolynomial.merge (SparsePolynomial.scale (23616 : Int) atom0128) (SparsePolynomial.scale (22464 : Int) atom0129))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (59328 : Int) atom0130) (SparsePolynomial.scale (20160 : Int) atom0131)) (SparsePolynomial.merge (SparsePolynomial.scale (30912 : Int) atom0132) (SparsePolynomial.merge (SparsePolynomial.scale (17856 : Int) atom0133) (SparsePolynomial.scale (22080 : Int) atom0134)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24960 : Int) atom0135) (SparsePolynomial.scale (38208 : Int) atom0136)) (SparsePolynomial.merge (SparsePolynomial.scale (40320 : Int) atom0137) (SparsePolynomial.merge (SparsePolynomial.scale (122688 : Int) atom0138) (SparsePolynomial.scale (52992 : Int) atom0139)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (83136 : Int) atom0140) (SparsePolynomial.scale (65664 : Int) atom0141)) (SparsePolynomial.merge (SparsePolynomial.scale (52272 : Int) atom0142) (SparsePolynomial.merge (SparsePolynomial.scale (84864 : Int) atom0143) (SparsePolynomial.scale (30336 : Int) atom0144)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62016 : Int) atom0145) (SparsePolynomial.scale (126720 : Int) atom0146)) (SparsePolynomial.merge (SparsePolynomial.scale (74496 : Int) atom0147) (SparsePolynomial.merge (SparsePolynomial.scale (104448 : Int) atom0148) (SparsePolynomial.scale (95616 : Int) atom0149))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (90240 : Int) atom0150) (SparsePolynomial.scale (132096 : Int) atom0151)) (SparsePolynomial.merge (SparsePolynomial.scale (43200 : Int) atom0152) (SparsePolynomial.merge (SparsePolynomial.scale (130752 : Int) atom0153) (SparsePolynomial.scale (96768 : Int) atom0154)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (125760 : Int) atom0155) (SparsePolynomial.scale (125568 : Int) atom0156)) (SparsePolynomial.merge (SparsePolynomial.scale (114624 : Int) atom0157) (SparsePolynomial.merge (SparsePolynomial.scale (179328 : Int) atom0158) (SparsePolynomial.scale (105408 : Int) atom0159)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block001 := by
  rw [block001_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0080_nonneg g hg hA hB) (atom0081_nonneg g hg hA hB)) (add_nonneg (atom0082_nonneg g hg hA hB) (add_nonneg (atom0083_nonneg g hg hA hB) (atom0084_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0085_nonneg g hg hA hB) (atom0086_nonneg g hg hA hB)) (add_nonneg (atom0087_nonneg g hg hA hB) (add_nonneg (atom0088_nonneg g hg hA hB) (atom0089_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0090_nonneg g hg hA hB) (atom0091_nonneg g hg hA hB)) (add_nonneg (atom0092_nonneg g hg hA hB) (add_nonneg (atom0093_nonneg g hg hA hB) (atom0094_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0095_nonneg g hg hA hB) (atom0096_nonneg g hg hA hB)) (add_nonneg (atom0097_nonneg g hg hA hB) (add_nonneg (atom0098_nonneg g hg hA hB) (atom0099_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0100_nonneg g hg hA hB) (atom0101_nonneg g hg hA hB)) (add_nonneg (atom0102_nonneg g hg hA hB) (add_nonneg (atom0103_nonneg g hg hA hB) (atom0104_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0105_nonneg g hg hA hB) (atom0106_nonneg g hg hA hB)) (add_nonneg (atom0107_nonneg g hg hA hB) (add_nonneg (atom0108_nonneg g hg hA hB) (atom0109_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0110_nonneg g hg hA hB) (atom0111_nonneg g hg hA hB)) (add_nonneg (atom0112_nonneg g hg hA hB) (add_nonneg (atom0113_nonneg g hg hA hB) (atom0114_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0115_nonneg g hg hA hB) (atom0116_nonneg g hg hA hB)) (add_nonneg (atom0117_nonneg g hg hA hB) (add_nonneg (atom0118_nonneg g hg hA hB) (atom0119_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0120_nonneg g hg hA hB) (atom0121_nonneg g hg hA hB)) (add_nonneg (atom0122_nonneg g hg hA hB) (add_nonneg (atom0123_nonneg g hg hA hB) (atom0124_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0125_nonneg g hg hA hB) (atom0126_nonneg g hg hA hB)) (add_nonneg (atom0127_nonneg g hg hA hB) (add_nonneg (atom0128_nonneg g hg hA hB) (atom0129_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0130_nonneg g hg hA hB) (atom0131_nonneg g hg hA hB)) (add_nonneg (atom0132_nonneg g hg hA hB) (add_nonneg (atom0133_nonneg g hg hA hB) (atom0134_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0135_nonneg g hg hA hB) (atom0136_nonneg g hg hA hB)) (add_nonneg (atom0137_nonneg g hg hA hB) (add_nonneg (atom0138_nonneg g hg hA hB) (atom0139_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0140_nonneg g hg hA hB) (atom0141_nonneg g hg hA hB)) (add_nonneg (atom0142_nonneg g hg hA hB) (add_nonneg (atom0143_nonneg g hg hA hB) (atom0144_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0145_nonneg g hg hA hB) (atom0146_nonneg g hg hA hB)) (add_nonneg (atom0147_nonneg g hg hA hB) (add_nonneg (atom0148_nonneg g hg hA hB) (atom0149_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0150_nonneg g hg hA hB) (atom0151_nonneg g hg hA hB)) (add_nonneg (atom0152_nonneg g hg hA hB) (add_nonneg (atom0153_nonneg g hg hA hB) (atom0154_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0155_nonneg g hg hA hB) (atom0156_nonneg g hg hA hB)) (add_nonneg (atom0157_nonneg g hg hA hB) (add_nonneg (atom0158_nonneg g hg hA hB) (atom0159_nonneg g hg hA hB))))))))

end APPT.Finite12
