import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0176 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0176 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0176 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0176_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5302217692800 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177 : SparsePolynomial.Poly := [([0,1,17], 1)]
theorem eval_atom0177 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0177 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0177_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1801017590400 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178 : SparsePolynomial.Poly := [([0,1,18], 1)]
theorem eval_atom0178 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0178 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0178_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (787190140800 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179 : SparsePolynomial.Poly := [([0,1,19], 1)]
theorem eval_atom0179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0179 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (420253545600 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0180 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0180 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0180_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7838074944000 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0181 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0181 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0181_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16012481587200 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0182 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0182 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0182_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16348813286400 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0183 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16685144985600 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0184 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0184 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0184_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17021476684800 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0185 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0185 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0185_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17357808384000 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0186 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17694140083200 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0187 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18030471782400 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0188 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18366803481600 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0189 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18703135180800 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0190 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19039466880000 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0191 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19375798579200 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0192 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19712130278400 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0193 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22980733171200 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0194 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0194 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0194_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13269638592000 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195 : SparsePolynomial.Poly := [([0,2,17], 1)]
theorem eval_atom0195 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0195 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0195_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10896850944000 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196 : SparsePolynomial.Poly := [([0,2,18], 1)]
theorem eval_atom0196 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0196 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0196_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1702920844800 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197 : SparsePolynomial.Poly := [([0,2,19], 1)]
theorem eval_atom0197 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0197 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0197_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2888296790400 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0198 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0198 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0198_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7747226726400 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0199 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0199 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0199_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15998951001600 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0200 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0200 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0200_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16503448550400 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0201 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0201 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0201_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17007946099200 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0202 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17512443648000 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0203 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0203 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0203_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18016941196800 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0204 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0204 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0204_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18521438745600 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0205 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0205 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0205_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19025936294400 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0206 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0206 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0206_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19530433843200 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0207 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0207 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0207_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20034931392000 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0208 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0208 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0208_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20539428940800 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0209 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0209 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0209_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21043926489600 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210 : SparsePolynomial.Poly := [([0,3,15], 1)]
theorem eval_atom0210 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0210 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0210_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24373900252800 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211 : SparsePolynomial.Poly := [([0,3,16], 1)]
theorem eval_atom0211 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0211 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0211_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15288112022400 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212 : SparsePolynomial.Poly := [([0,3,17], 1)]
theorem eval_atom0212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0212 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11985579849600 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213 : SparsePolynomial.Poly := [([0,3,18], 1)]
theorem eval_atom0213 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0213 = ((g 0) * (g 3) * (g 18)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0213_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3766818384000 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214 : SparsePolynomial.Poly := [([0,3,19], 1)]
theorem eval_atom0214 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0214 = ((g 0) * (g 3) * (g 19)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0214_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5075419305600 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215 : SparsePolynomial.Poly := [([0,3,20], 1)]
theorem eval_atom0215 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0215 = ((g 0) * (g 3) * (g 20)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0215_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (389970806400 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0216 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0216 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0216_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8898776208000 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0217 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0217 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0217_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16329426810624 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0218 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0218 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0218_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16994415513600 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0219 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0219 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0219_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17667078912000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0220 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0220 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0220_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18339742310400 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0221 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0221 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0221_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19012405708800 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0222 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0222 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0222_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19685069107200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0223 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0223 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0223_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20357732505600 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0224 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0224 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0224_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21233148865600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0225 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0225 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0225_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22067177025600 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0226 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0226 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0226_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22681852200000 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227 : SparsePolynomial.Poly := [([0,4,15], 1)]
theorem eval_atom0227 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0227 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0227_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25767067334400 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228 : SparsePolynomial.Poly := [([0,4,16], 1)]
theorem eval_atom0228 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0228 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0228_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17557535532600 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229 : SparsePolynomial.Poly := [([0,4,17], 1)]
theorem eval_atom0229 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0229 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0229_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13074308755200 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230 : SparsePolynomial.Poly := [([0,4,18], 1)]
theorem eval_atom0230 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0230 = ((g 0) * (g 4) * (g 18)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0230_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6011898921000 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231 : SparsePolynomial.Poly := [([0,4,19], 1)]
theorem eval_atom0231 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0231 = ((g 0) * (g 4) * (g 19)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0231_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7268672867400 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232 : SparsePolynomial.Poly := [([0,4,20], 1)]
theorem eval_atom0232 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0232 = ((g 0) * (g 4) * (g 20)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0232_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2531397393000 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0233 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0233 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0233_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10430034421248 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0234 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0234 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0234_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18863725537728 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0235 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0235 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0235_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18055888573248 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0236 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0236 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0236_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18662543424000 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0237 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0237 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0237_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19685793960000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0238 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0238 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0238_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20344201920000 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0239 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0239 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0239_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21185031168000 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240 : SparsePolynomial.Poly := [([0,5,12], 1)]
theorem eval_atom0240 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0240 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0240_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22373100702400 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241 : SparsePolynomial.Poly := [([0,5,13], 1)]
theorem eval_atom0241 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0241 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0241_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23206404009600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242 : SparsePolynomial.Poly := [([0,5,14], 1)]
theorem eval_atom0242 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0242 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0242_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23885832700800 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243 : SparsePolynomial.Poly := [([0,5,15], 1)]
theorem eval_atom0243 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0243 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0243_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27533078906688 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244 : SparsePolynomial.Poly := [([0,5,16], 1)]
theorem eval_atom0244 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0244 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0244_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19930254363648 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245 : SparsePolynomial.Poly := [([0,5,17], 1)]
theorem eval_atom0245 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0245 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0245_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16772949095616 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246 : SparsePolynomial.Poly := [([0,5,18], 1)]
theorem eval_atom0246 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0246 = ((g 0) * (g 5) * (g 18)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0246_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10592587378944 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247 : SparsePolynomial.Poly := [([0,5,19], 1)]
theorem eval_atom0247 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0247 = ((g 0) * (g 5) * (g 19)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0247_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11062689626880 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248 : SparsePolynomial.Poly := [([0,5,20], 1)]
theorem eval_atom0248 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0248 = ((g 0) * (g 5) * (g 20)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0248_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7775809398144 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0249 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0249 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0249_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13029789427200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0250 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0250 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0250_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22027546931328 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0251 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0251 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0251_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20547763034400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0252 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0252 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0252_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20553442761600 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0253 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0253 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0253_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21299316292800 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0254 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0254 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0254_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22058417203200 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255 : SparsePolynomial.Poly := [([0,6,12], 1)]
theorem eval_atom0255 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0255 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0255_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23415680646400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block004 : SparsePolynomial.Poly := [([0,1,16], 5302217692800), ([0,1,17], 1801017590400), ([0,1,18], 787190140800), ([0,1,19], 420253545600), ([0,2,2], 7838074944000), ([0,2,3], 16012481587200), ([0,2,4], 16348813286400), ([0,2,5], 16685144985600), ([0,2,6], 17021476684800), ([0,2,7], 17357808384000), ([0,2,8], 17694140083200), ([0,2,9], 18030471782400), ([0,2,10], 18366803481600), ([0,2,11], 18703135180800), ([0,2,12], 19039466880000), ([0,2,13], 19375798579200), ([0,2,14], 19712130278400), ([0,2,15], 22980733171200), ([0,2,16], 13269638592000), ([0,2,17], 10896850944000), ([0,2,18], 1702920844800), ([0,2,19], 2888296790400), ([0,3,3], 7747226726400), ([0,3,4], 15998951001600), ([0,3,5], 16503448550400), ([0,3,6], 17007946099200), ([0,3,7], 17512443648000), ([0,3,8], 18016941196800), ([0,3,9], 18521438745600), ([0,3,10], 19025936294400), ([0,3,11], 19530433843200), ([0,3,12], 20034931392000), ([0,3,13], 20539428940800), ([0,3,14], 21043926489600), ([0,3,15], 24373900252800), ([0,3,16], 15288112022400), ([0,3,17], 11985579849600), ([0,3,18], 3766818384000), ([0,3,19], 5075419305600), ([0,3,20], 389970806400), ([0,4,4], 8898776208000), ([0,4,5], 16329426810624), ([0,4,6], 16994415513600), ([0,4,7], 17667078912000), ([0,4,8], 18339742310400), ([0,4,9], 19012405708800), ([0,4,10], 19685069107200), ([0,4,11], 20357732505600), ([0,4,12], 21233148865600), ([0,4,13], 22067177025600), ([0,4,14], 22681852200000), ([0,4,15], 25767067334400), ([0,4,16], 17557535532600), ([0,4,17], 13074308755200), ([0,4,18], 6011898921000), ([0,4,19], 7268672867400), ([0,4,20], 2531397393000), ([0,5,5], 10430034421248), ([0,5,6], 18863725537728), ([0,5,7], 18055888573248), ([0,5,8], 18662543424000), ([0,5,9], 19685793960000), ([0,5,10], 20344201920000), ([0,5,11], 21185031168000), ([0,5,12], 22373100702400), ([0,5,13], 23206404009600), ([0,5,14], 23885832700800), ([0,5,15], 27533078906688), ([0,5,16], 19930254363648), ([0,5,17], 16772949095616), ([0,5,18], 10592587378944), ([0,5,19], 11062689626880), ([0,5,20], 7775809398144), ([0,6,6], 13029789427200), ([0,6,7], 22027546931328), ([0,6,8], 20547763034400), ([0,6,9], 20553442761600), ([0,6,10], 21299316292800), ([0,6,11], 22058417203200), ([0,6,12], 23415680646400)]
theorem block004_data : block004 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5302217692800 : Int) atom0176) (SparsePolynomial.scale (1801017590400 : Int) atom0177)) (SparsePolynomial.merge (SparsePolynomial.scale (787190140800 : Int) atom0178) (SparsePolynomial.merge (SparsePolynomial.scale (420253545600 : Int) atom0179) (SparsePolynomial.scale (7838074944000 : Int) atom0180)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16012481587200 : Int) atom0181) (SparsePolynomial.scale (16348813286400 : Int) atom0182)) (SparsePolynomial.merge (SparsePolynomial.scale (16685144985600 : Int) atom0183) (SparsePolynomial.merge (SparsePolynomial.scale (17021476684800 : Int) atom0184) (SparsePolynomial.scale (17357808384000 : Int) atom0185))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17694140083200 : Int) atom0186) (SparsePolynomial.scale (18030471782400 : Int) atom0187)) (SparsePolynomial.merge (SparsePolynomial.scale (18366803481600 : Int) atom0188) (SparsePolynomial.merge (SparsePolynomial.scale (18703135180800 : Int) atom0189) (SparsePolynomial.scale (19039466880000 : Int) atom0190)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19375798579200 : Int) atom0191) (SparsePolynomial.scale (19712130278400 : Int) atom0192)) (SparsePolynomial.merge (SparsePolynomial.scale (22980733171200 : Int) atom0193) (SparsePolynomial.merge (SparsePolynomial.scale (13269638592000 : Int) atom0194) (SparsePolynomial.scale (10896850944000 : Int) atom0195)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1702920844800 : Int) atom0196) (SparsePolynomial.scale (2888296790400 : Int) atom0197)) (SparsePolynomial.merge (SparsePolynomial.scale (7747226726400 : Int) atom0198) (SparsePolynomial.merge (SparsePolynomial.scale (15998951001600 : Int) atom0199) (SparsePolynomial.scale (16503448550400 : Int) atom0200)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17007946099200 : Int) atom0201) (SparsePolynomial.scale (17512443648000 : Int) atom0202)) (SparsePolynomial.merge (SparsePolynomial.scale (18016941196800 : Int) atom0203) (SparsePolynomial.merge (SparsePolynomial.scale (18521438745600 : Int) atom0204) (SparsePolynomial.scale (19025936294400 : Int) atom0205))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19530433843200 : Int) atom0206) (SparsePolynomial.scale (20034931392000 : Int) atom0207)) (SparsePolynomial.merge (SparsePolynomial.scale (20539428940800 : Int) atom0208) (SparsePolynomial.merge (SparsePolynomial.scale (21043926489600 : Int) atom0209) (SparsePolynomial.scale (24373900252800 : Int) atom0210)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15288112022400 : Int) atom0211) (SparsePolynomial.scale (11985579849600 : Int) atom0212)) (SparsePolynomial.merge (SparsePolynomial.scale (3766818384000 : Int) atom0213) (SparsePolynomial.merge (SparsePolynomial.scale (5075419305600 : Int) atom0214) (SparsePolynomial.scale (389970806400 : Int) atom0215))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8898776208000 : Int) atom0216) (SparsePolynomial.scale (16329426810624 : Int) atom0217)) (SparsePolynomial.merge (SparsePolynomial.scale (16994415513600 : Int) atom0218) (SparsePolynomial.merge (SparsePolynomial.scale (17667078912000 : Int) atom0219) (SparsePolynomial.scale (18339742310400 : Int) atom0220)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19012405708800 : Int) atom0221) (SparsePolynomial.scale (19685069107200 : Int) atom0222)) (SparsePolynomial.merge (SparsePolynomial.scale (20357732505600 : Int) atom0223) (SparsePolynomial.merge (SparsePolynomial.scale (21233148865600 : Int) atom0224) (SparsePolynomial.scale (22067177025600 : Int) atom0225))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22681852200000 : Int) atom0226) (SparsePolynomial.scale (25767067334400 : Int) atom0227)) (SparsePolynomial.merge (SparsePolynomial.scale (17557535532600 : Int) atom0228) (SparsePolynomial.merge (SparsePolynomial.scale (13074308755200 : Int) atom0229) (SparsePolynomial.scale (6011898921000 : Int) atom0230)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7268672867400 : Int) atom0231) (SparsePolynomial.scale (2531397393000 : Int) atom0232)) (SparsePolynomial.merge (SparsePolynomial.scale (10430034421248 : Int) atom0233) (SparsePolynomial.merge (SparsePolynomial.scale (18863725537728 : Int) atom0234) (SparsePolynomial.scale (18055888573248 : Int) atom0235)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18662543424000 : Int) atom0236) (SparsePolynomial.scale (19685793960000 : Int) atom0237)) (SparsePolynomial.merge (SparsePolynomial.scale (20344201920000 : Int) atom0238) (SparsePolynomial.merge (SparsePolynomial.scale (21185031168000 : Int) atom0239) (SparsePolynomial.scale (22373100702400 : Int) atom0240)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23206404009600 : Int) atom0241) (SparsePolynomial.scale (23885832700800 : Int) atom0242)) (SparsePolynomial.merge (SparsePolynomial.scale (27533078906688 : Int) atom0243) (SparsePolynomial.merge (SparsePolynomial.scale (19930254363648 : Int) atom0244) (SparsePolynomial.scale (16772949095616 : Int) atom0245))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10592587378944 : Int) atom0246) (SparsePolynomial.scale (11062689626880 : Int) atom0247)) (SparsePolynomial.merge (SparsePolynomial.scale (7775809398144 : Int) atom0248) (SparsePolynomial.merge (SparsePolynomial.scale (13029789427200 : Int) atom0249) (SparsePolynomial.scale (22027546931328 : Int) atom0250)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20547763034400 : Int) atom0251) (SparsePolynomial.scale (20553442761600 : Int) atom0252)) (SparsePolynomial.merge (SparsePolynomial.scale (21299316292800 : Int) atom0253) (SparsePolynomial.merge (SparsePolynomial.scale (22058417203200 : Int) atom0254) (SparsePolynomial.scale (23415680646400 : Int) atom0255)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block004 := by
  rw [block004_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0176_nonneg g hg hA hB) (atom0177_nonneg g hg hA hB)) (add_nonneg (atom0178_nonneg g hg hA hB) (add_nonneg (atom0179_nonneg g hg hA hB) (atom0180_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0181_nonneg g hg hA hB) (atom0182_nonneg g hg hA hB)) (add_nonneg (atom0183_nonneg g hg hA hB) (add_nonneg (atom0184_nonneg g hg hA hB) (atom0185_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0186_nonneg g hg hA hB) (atom0187_nonneg g hg hA hB)) (add_nonneg (atom0188_nonneg g hg hA hB) (add_nonneg (atom0189_nonneg g hg hA hB) (atom0190_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0191_nonneg g hg hA hB) (atom0192_nonneg g hg hA hB)) (add_nonneg (atom0193_nonneg g hg hA hB) (add_nonneg (atom0194_nonneg g hg hA hB) (atom0195_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0196_nonneg g hg hA hB) (atom0197_nonneg g hg hA hB)) (add_nonneg (atom0198_nonneg g hg hA hB) (add_nonneg (atom0199_nonneg g hg hA hB) (atom0200_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0201_nonneg g hg hA hB) (atom0202_nonneg g hg hA hB)) (add_nonneg (atom0203_nonneg g hg hA hB) (add_nonneg (atom0204_nonneg g hg hA hB) (atom0205_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0206_nonneg g hg hA hB) (atom0207_nonneg g hg hA hB)) (add_nonneg (atom0208_nonneg g hg hA hB) (add_nonneg (atom0209_nonneg g hg hA hB) (atom0210_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0211_nonneg g hg hA hB) (atom0212_nonneg g hg hA hB)) (add_nonneg (atom0213_nonneg g hg hA hB) (add_nonneg (atom0214_nonneg g hg hA hB) (atom0215_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0216_nonneg g hg hA hB) (atom0217_nonneg g hg hA hB)) (add_nonneg (atom0218_nonneg g hg hA hB) (add_nonneg (atom0219_nonneg g hg hA hB) (atom0220_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0221_nonneg g hg hA hB) (atom0222_nonneg g hg hA hB)) (add_nonneg (atom0223_nonneg g hg hA hB) (add_nonneg (atom0224_nonneg g hg hA hB) (atom0225_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0226_nonneg g hg hA hB) (atom0227_nonneg g hg hA hB)) (add_nonneg (atom0228_nonneg g hg hA hB) (add_nonneg (atom0229_nonneg g hg hA hB) (atom0230_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0231_nonneg g hg hA hB) (atom0232_nonneg g hg hA hB)) (add_nonneg (atom0233_nonneg g hg hA hB) (add_nonneg (atom0234_nonneg g hg hA hB) (atom0235_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0236_nonneg g hg hA hB) (atom0237_nonneg g hg hA hB)) (add_nonneg (atom0238_nonneg g hg hA hB) (add_nonneg (atom0239_nonneg g hg hA hB) (atom0240_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0241_nonneg g hg hA hB) (atom0242_nonneg g hg hA hB)) (add_nonneg (atom0243_nonneg g hg hA hB) (add_nonneg (atom0244_nonneg g hg hA hB) (atom0245_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0246_nonneg g hg hA hB) (atom0247_nonneg g hg hA hB)) (add_nonneg (atom0248_nonneg g hg hA hB) (add_nonneg (atom0249_nonneg g hg hA hB) (atom0250_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0251_nonneg g hg hA hB) (atom0252_nonneg g hg hA hB)) (add_nonneg (atom0253_nonneg g hg hA hB) (add_nonneg (atom0254_nonneg g hg hA hB) (atom0255_nonneg g hg hA hB))))))))

end APPT.Finite21
