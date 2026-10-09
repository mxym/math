import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0073 : SparsePolynomial.Poly := [([0,0,11], 1)]
theorem eval_atom0073 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0073 = ((g 0) * (g 0) * (g 11)) := by
  norm_num [atom0073, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0073_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4008960 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 0) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074 : SparsePolynomial.Poly := [([0,0,12], 1)]
theorem eval_atom0074 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0074 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0074, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0074_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2108160 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0075 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0075 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0075, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0075_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2816640 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0076 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0076 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0076, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0076_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21556800 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0077 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0077 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0077, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0077_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21798720 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0078 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0078 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0078, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0078_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22040640 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0079 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0079 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0079, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0079_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22282560 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0080 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0080 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0080_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22524480 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0081 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0081 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0081_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22766400 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0082 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0082 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0082_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23878080 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0083 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0083 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0083_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47524320 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0084 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0084 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0084_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19913040 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0085 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0085 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0085_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8791200 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0086 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0086 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0086_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4471920 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0087 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0087 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0087_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2792880 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0088 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0088 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0088_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24606720 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0089 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0089 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0089_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51598080 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0090 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0090 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0090_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53982720 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0091 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0091 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0091_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56367360 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0092 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0092 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0092_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58752000 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0093 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0093 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0093_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61136640 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0094 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0094 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0094_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63521280 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0095 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0095 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0095_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (80002080 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0096 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0096 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0096_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48319200 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0097 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0097 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0097_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33558840 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0098 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0098 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0098_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9119520 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0099 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0099 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0099_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10851840 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0100 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0100 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0100_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25790400 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0101 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0101 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0101_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53758080 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0102 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0102 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0102_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57335040 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0103 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0103 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0103_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60912000 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0104 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0104 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0104_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64601280 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0105 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0105 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0105_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68290560 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0106 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0106 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0106_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (85263840 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0107 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0107 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0107_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54403380 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0108 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0108 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0108_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38354040 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0109 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0109 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0109_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15224220 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0110 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0110 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0110_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18271980 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0111 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0111 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0111_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1041660 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0112 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0112 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0112_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33416640 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0113 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0113 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0113_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62148960 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0114 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0114 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0114_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (66313440 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0115 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0115 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0115_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70477920 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0116 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0116 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0116_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74642400 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0117 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0117 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0117_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90525600 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0118 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0118 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0118_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61395660 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0119 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0119 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0119_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43149240 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0120 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0120 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0120_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22546980 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0121 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0121 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0121_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25656660 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0122 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0122 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0122_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8488260 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0123 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0123 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0123_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39827520 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0124 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0124 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0124_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74807712 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0125 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0125 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0125_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77670720 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0126 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0126 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0126_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82012320 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0127 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0127 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0127_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (95787360 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0128 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0128 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0128_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68358420 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0129 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0129 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0129_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47944440 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([0,5,12], 1)]
theorem eval_atom0130 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0130 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0130_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28341180 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([0,5,13], 1)]
theorem eval_atom0131 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0131 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0131_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30612780 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([0,5,14], 1)]
theorem eval_atom0132 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0132 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0132_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12606300 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0133 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0133 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0133_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47183040 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0134 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0134 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0134_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89196672 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0135 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0135 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0135_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89320320 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0136 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0136 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0136_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101049120 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0137 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0137 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0137_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74616660 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0138 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0138 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0138_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52739640 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([0,6,12], 1)]
theorem eval_atom0139 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0139 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0139_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32741820 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([0,6,13], 1)]
theorem eval_atom0140 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0140 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0140_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33815340 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([0,6,14], 1)]
theorem eval_atom0141 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0141 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0141_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14610780 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0142 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0142 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0142_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54378240 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0143 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0143 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0143_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102218720 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([0,7,9], 1)]
theorem eval_atom0144 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0144 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0144_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (106800960 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([0,7,10], 1)]
theorem eval_atom0145 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0145 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0145_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (80515680 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([0,7,11], 1)]
theorem eval_atom0146 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0146 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0146_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57534840 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([0,7,12], 1)]
theorem eval_atom0147 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0147 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0147_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35679840 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([0,7,13], 1)]
theorem eval_atom0148 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0148 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0148_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34919040 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([0,7,14], 1)]
theorem eval_atom0149 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0149 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0149_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13880160 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0150 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0150 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0150_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60480000 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([0,8,9], 1)]
theorem eval_atom0151 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0151 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0151_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114342840 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([0,8,10], 1)]
theorem eval_atom0152 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0152 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0152_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86347080 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block001 : SparsePolynomial.Poly := [([0,0,11], 4008960), ([0,0,12], 2108160), ([0,1,1], 2816640), ([0,1,2], 21556800), ([0,1,3], 21798720), ([0,1,4], 22040640), ([0,1,5], 22282560), ([0,1,6], 22524480), ([0,1,7], 22766400), ([0,1,8], 23878080), ([0,1,9], 47524320), ([0,1,10], 19913040), ([0,1,11], 8791200), ([0,1,12], 4471920), ([0,1,13], 2792880), ([0,2,2], 24606720), ([0,2,3], 51598080), ([0,2,4], 53982720), ([0,2,5], 56367360), ([0,2,6], 58752000), ([0,2,7], 61136640), ([0,2,8], 63521280), ([0,2,9], 80002080), ([0,2,10], 48319200), ([0,2,11], 33558840), ([0,2,12], 9119520), ([0,2,13], 10851840), ([0,3,3], 25790400), ([0,3,4], 53758080), ([0,3,5], 57335040), ([0,3,6], 60912000), ([0,3,7], 64601280), ([0,3,8], 68290560), ([0,3,9], 85263840), ([0,3,10], 54403380), ([0,3,11], 38354040), ([0,3,12], 15224220), ([0,3,13], 18271980), ([0,3,14], 1041660), ([0,4,4], 33416640), ([0,4,5], 62148960), ([0,4,6], 66313440), ([0,4,7], 70477920), ([0,4,8], 74642400), ([0,4,9], 90525600), ([0,4,10], 61395660), ([0,4,11], 43149240), ([0,4,12], 22546980), ([0,4,13], 25656660), ([0,4,14], 8488260), ([0,5,5], 39827520), ([0,5,6], 74807712), ([0,5,7], 77670720), ([0,5,8], 82012320), ([0,5,9], 95787360), ([0,5,10], 68358420), ([0,5,11], 47944440), ([0,5,12], 28341180), ([0,5,13], 30612780), ([0,5,14], 12606300), ([0,6,6], 47183040), ([0,6,7], 89196672), ([0,6,8], 89320320), ([0,6,9], 101049120), ([0,6,10], 74616660), ([0,6,11], 52739640), ([0,6,12], 32741820), ([0,6,13], 33815340), ([0,6,14], 14610780), ([0,7,7], 54378240), ([0,7,8], 102218720), ([0,7,9], 106800960), ([0,7,10], 80515680), ([0,7,11], 57534840), ([0,7,12], 35679840), ([0,7,13], 34919040), ([0,7,14], 13880160), ([0,8,8], 60480000), ([0,8,9], 114342840), ([0,8,10], 86347080)]
theorem block001_data : block001 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4008960 : Int) atom0073) (SparsePolynomial.scale (2108160 : Int) atom0074)) (SparsePolynomial.merge (SparsePolynomial.scale (2816640 : Int) atom0075) (SparsePolynomial.merge (SparsePolynomial.scale (21556800 : Int) atom0076) (SparsePolynomial.scale (21798720 : Int) atom0077)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22040640 : Int) atom0078) (SparsePolynomial.scale (22282560 : Int) atom0079)) (SparsePolynomial.merge (SparsePolynomial.scale (22524480 : Int) atom0080) (SparsePolynomial.merge (SparsePolynomial.scale (22766400 : Int) atom0081) (SparsePolynomial.scale (23878080 : Int) atom0082))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47524320 : Int) atom0083) (SparsePolynomial.scale (19913040 : Int) atom0084)) (SparsePolynomial.merge (SparsePolynomial.scale (8791200 : Int) atom0085) (SparsePolynomial.merge (SparsePolynomial.scale (4471920 : Int) atom0086) (SparsePolynomial.scale (2792880 : Int) atom0087)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24606720 : Int) atom0088) (SparsePolynomial.scale (51598080 : Int) atom0089)) (SparsePolynomial.merge (SparsePolynomial.scale (53982720 : Int) atom0090) (SparsePolynomial.merge (SparsePolynomial.scale (56367360 : Int) atom0091) (SparsePolynomial.scale (58752000 : Int) atom0092)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61136640 : Int) atom0093) (SparsePolynomial.scale (63521280 : Int) atom0094)) (SparsePolynomial.merge (SparsePolynomial.scale (80002080 : Int) atom0095) (SparsePolynomial.merge (SparsePolynomial.scale (48319200 : Int) atom0096) (SparsePolynomial.scale (33558840 : Int) atom0097)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9119520 : Int) atom0098) (SparsePolynomial.scale (10851840 : Int) atom0099)) (SparsePolynomial.merge (SparsePolynomial.scale (25790400 : Int) atom0100) (SparsePolynomial.merge (SparsePolynomial.scale (53758080 : Int) atom0101) (SparsePolynomial.scale (57335040 : Int) atom0102))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (60912000 : Int) atom0103) (SparsePolynomial.scale (64601280 : Int) atom0104)) (SparsePolynomial.merge (SparsePolynomial.scale (68290560 : Int) atom0105) (SparsePolynomial.merge (SparsePolynomial.scale (85263840 : Int) atom0106) (SparsePolynomial.scale (54403380 : Int) atom0107)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38354040 : Int) atom0108) (SparsePolynomial.scale (15224220 : Int) atom0109)) (SparsePolynomial.merge (SparsePolynomial.scale (18271980 : Int) atom0110) (SparsePolynomial.merge (SparsePolynomial.scale (1041660 : Int) atom0111) (SparsePolynomial.scale (33416640 : Int) atom0112))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62148960 : Int) atom0113) (SparsePolynomial.scale (66313440 : Int) atom0114)) (SparsePolynomial.merge (SparsePolynomial.scale (70477920 : Int) atom0115) (SparsePolynomial.merge (SparsePolynomial.scale (74642400 : Int) atom0116) (SparsePolynomial.scale (90525600 : Int) atom0117)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61395660 : Int) atom0118) (SparsePolynomial.scale (43149240 : Int) atom0119)) (SparsePolynomial.merge (SparsePolynomial.scale (22546980 : Int) atom0120) (SparsePolynomial.merge (SparsePolynomial.scale (25656660 : Int) atom0121) (SparsePolynomial.scale (8488260 : Int) atom0122))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39827520 : Int) atom0123) (SparsePolynomial.scale (74807712 : Int) atom0124)) (SparsePolynomial.merge (SparsePolynomial.scale (77670720 : Int) atom0125) (SparsePolynomial.merge (SparsePolynomial.scale (82012320 : Int) atom0126) (SparsePolynomial.scale (95787360 : Int) atom0127)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68358420 : Int) atom0128) (SparsePolynomial.scale (47944440 : Int) atom0129)) (SparsePolynomial.merge (SparsePolynomial.scale (28341180 : Int) atom0130) (SparsePolynomial.merge (SparsePolynomial.scale (30612780 : Int) atom0131) (SparsePolynomial.scale (12606300 : Int) atom0132)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47183040 : Int) atom0133) (SparsePolynomial.scale (89196672 : Int) atom0134)) (SparsePolynomial.merge (SparsePolynomial.scale (89320320 : Int) atom0135) (SparsePolynomial.merge (SparsePolynomial.scale (101049120 : Int) atom0136) (SparsePolynomial.scale (74616660 : Int) atom0137)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52739640 : Int) atom0138) (SparsePolynomial.scale (32741820 : Int) atom0139)) (SparsePolynomial.merge (SparsePolynomial.scale (33815340 : Int) atom0140) (SparsePolynomial.merge (SparsePolynomial.scale (14610780 : Int) atom0141) (SparsePolynomial.scale (54378240 : Int) atom0142))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (102218720 : Int) atom0143) (SparsePolynomial.scale (106800960 : Int) atom0144)) (SparsePolynomial.merge (SparsePolynomial.scale (80515680 : Int) atom0145) (SparsePolynomial.merge (SparsePolynomial.scale (57534840 : Int) atom0146) (SparsePolynomial.scale (35679840 : Int) atom0147)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34919040 : Int) atom0148) (SparsePolynomial.scale (13880160 : Int) atom0149)) (SparsePolynomial.merge (SparsePolynomial.scale (60480000 : Int) atom0150) (SparsePolynomial.merge (SparsePolynomial.scale (114342840 : Int) atom0151) (SparsePolynomial.scale (86347080 : Int) atom0152)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block001 := by
  rw [block001_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0073_nonneg g hg hA hB) (atom0074_nonneg g hg hA hB)) (add_nonneg (atom0075_nonneg g hg hA hB) (add_nonneg (atom0076_nonneg g hg hA hB) (atom0077_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0078_nonneg g hg hA hB) (atom0079_nonneg g hg hA hB)) (add_nonneg (atom0080_nonneg g hg hA hB) (add_nonneg (atom0081_nonneg g hg hA hB) (atom0082_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0083_nonneg g hg hA hB) (atom0084_nonneg g hg hA hB)) (add_nonneg (atom0085_nonneg g hg hA hB) (add_nonneg (atom0086_nonneg g hg hA hB) (atom0087_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0088_nonneg g hg hA hB) (atom0089_nonneg g hg hA hB)) (add_nonneg (atom0090_nonneg g hg hA hB) (add_nonneg (atom0091_nonneg g hg hA hB) (atom0092_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0093_nonneg g hg hA hB) (atom0094_nonneg g hg hA hB)) (add_nonneg (atom0095_nonneg g hg hA hB) (add_nonneg (atom0096_nonneg g hg hA hB) (atom0097_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0098_nonneg g hg hA hB) (atom0099_nonneg g hg hA hB)) (add_nonneg (atom0100_nonneg g hg hA hB) (add_nonneg (atom0101_nonneg g hg hA hB) (atom0102_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0103_nonneg g hg hA hB) (atom0104_nonneg g hg hA hB)) (add_nonneg (atom0105_nonneg g hg hA hB) (add_nonneg (atom0106_nonneg g hg hA hB) (atom0107_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0108_nonneg g hg hA hB) (atom0109_nonneg g hg hA hB)) (add_nonneg (atom0110_nonneg g hg hA hB) (add_nonneg (atom0111_nonneg g hg hA hB) (atom0112_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0113_nonneg g hg hA hB) (atom0114_nonneg g hg hA hB)) (add_nonneg (atom0115_nonneg g hg hA hB) (add_nonneg (atom0116_nonneg g hg hA hB) (atom0117_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0118_nonneg g hg hA hB) (atom0119_nonneg g hg hA hB)) (add_nonneg (atom0120_nonneg g hg hA hB) (add_nonneg (atom0121_nonneg g hg hA hB) (atom0122_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0123_nonneg g hg hA hB) (atom0124_nonneg g hg hA hB)) (add_nonneg (atom0125_nonneg g hg hA hB) (add_nonneg (atom0126_nonneg g hg hA hB) (atom0127_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0128_nonneg g hg hA hB) (atom0129_nonneg g hg hA hB)) (add_nonneg (atom0130_nonneg g hg hA hB) (add_nonneg (atom0131_nonneg g hg hA hB) (atom0132_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0133_nonneg g hg hA hB) (atom0134_nonneg g hg hA hB)) (add_nonneg (atom0135_nonneg g hg hA hB) (add_nonneg (atom0136_nonneg g hg hA hB) (atom0137_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0138_nonneg g hg hA hB) (atom0139_nonneg g hg hA hB)) (add_nonneg (atom0140_nonneg g hg hA hB) (add_nonneg (atom0141_nonneg g hg hA hB) (atom0142_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0143_nonneg g hg hA hB) (atom0144_nonneg g hg hA hB)) (add_nonneg (atom0145_nonneg g hg hA hB) (add_nonneg (atom0146_nonneg g hg hA hB) (atom0147_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0148_nonneg g hg hA hB) (atom0149_nonneg g hg hA hB)) (add_nonneg (atom0150_nonneg g hg hA hB) (add_nonneg (atom0151_nonneg g hg hA hB) (atom0152_nonneg g hg hA hB))))))))

end APPT.Finite15
