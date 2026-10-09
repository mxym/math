import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0175 : SparsePolynomial.Poly := [([0,4,15], 1)]
theorem eval_atom0175 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1360448880 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176 : SparsePolynomial.Poly := [([0,4,16], 1)]
theorem eval_atom0176 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1674024240 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177 : SparsePolynomial.Poly := [([0,4,17], 1)]
theorem eval_atom0177 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (703165680 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0178 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2579342400 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0179 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4516403328 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0180 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4367547360 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0181 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4567144800 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0182 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4768422240 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0183 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4983085920 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0184 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5216364000 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185 : SparsePolynomial.Poly := [([0,5,12], 1)]
theorem eval_atom0185 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5941555200 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186 : SparsePolynomial.Poly := [([0,5,13], 1)]
theorem eval_atom0186 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4162226220 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187 : SparsePolynomial.Poly := [([0,5,14], 1)]
theorem eval_atom0187 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3238888680 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188 : SparsePolynomial.Poly := [([0,5,15], 1)]
theorem eval_atom0188 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1754614980 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189 : SparsePolynomial.Poly := [([0,5,16], 1)]
theorem eval_atom0189 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2027377620 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190 : SparsePolynomial.Poly := [([0,5,17], 1)]
theorem eval_atom0190 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1015706340 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0191 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2842228800 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0192 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5214287808 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0193 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5033727840 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0194 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5249197920 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0195 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5464668000 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0196 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5698752480 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197 : SparsePolynomial.Poly := [([0,6,12], 1)]
theorem eval_atom0197 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6261373440 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198 : SparsePolynomial.Poly := [([0,6,13], 1)]
theorem eval_atom0198 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4589920620 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199 : SparsePolynomial.Poly := [([0,6,14], 1)]
theorem eval_atom0199 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3503549160 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200 : SparsePolynomial.Poly := [([0,6,15], 1)]
theorem eval_atom0200 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = ((g 0) * (g 6) * (g 15)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2071308420 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201 : SparsePolynomial.Poly := [([0,6,16], 1)]
theorem eval_atom0201 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = ((g 0) * (g 6) * (g 16)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2269801620 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202 : SparsePolynomial.Poly := [([0,6,17], 1)]
theorem eval_atom0202 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = ((g 0) * (g 6) * (g 17)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1183860900 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0203 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3277226880 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0204 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6038429568 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205 : SparsePolynomial.Poly := [([0,7,9], 1)]
theorem eval_atom0205 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5672303040 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206 : SparsePolynomial.Poly := [([0,7,10], 1)]
theorem eval_atom0206 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5875999680 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207 : SparsePolynomial.Poly := [([0,7,11], 1)]
theorem eval_atom0207 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6098310720 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208 : SparsePolynomial.Poly := [([0,7,12], 1)]
theorem eval_atom0208 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6581191680 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209 : SparsePolynomial.Poly := [([0,7,13], 1)]
theorem eval_atom0209 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4932461160 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210 : SparsePolynomial.Poly := [([0,7,14], 1)]
theorem eval_atom0210 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3768209640 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211 : SparsePolynomial.Poly := [([0,7,15], 1)]
theorem eval_atom0211 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = ((g 0) * (g 7) * (g 15)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2323360440 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212 : SparsePolynomial.Poly := [([0,7,16], 1)]
theorem eval_atom0212 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = ((g 0) * (g 7) * (g 16)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2465452440 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213 : SparsePolynomial.Poly := [([0,7,17], 1)]
theorem eval_atom0213 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = ((g 0) * (g 7) * (g 17)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1323110520 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0214 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3666370560 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215 : SparsePolynomial.Poly := [([0,8,9], 1)]
theorem eval_atom0215 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6875078400 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216 : SparsePolynomial.Poly := [([0,8,10], 1)]
theorem eval_atom0216 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6343352832 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217 : SparsePolynomial.Poly := [([0,8,11], 1)]
theorem eval_atom0217 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6498405120 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218 : SparsePolynomial.Poly := [([0,8,12], 1)]
theorem eval_atom0218 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6913818240 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219 : SparsePolynomial.Poly := [([0,8,13], 1)]
theorem eval_atom0219 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5270770560 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220 : SparsePolynomial.Poly := [([0,8,14], 1)]
theorem eval_atom0220 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4122528360 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221 : SparsePolynomial.Poly := [([0,8,15], 1)]
theorem eval_atom0221 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = ((g 0) * (g 8) * (g 15)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2586806400 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222 : SparsePolynomial.Poly := [([0,8,16], 1)]
theorem eval_atom0222 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = ((g 0) * (g 8) * (g 16)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2610257280 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223 : SparsePolynomial.Poly := [([0,8,17], 1)]
theorem eval_atom0223 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = ((g 0) * (g 8) * (g 17)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1426124160 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0224 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4060320000 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225 : SparsePolynomial.Poly := [([0,9,10], 1)]
theorem eval_atom0225 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7582617600 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226 : SparsePolynomial.Poly := [([0,9,11], 1)]
theorem eval_atom0226 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7116061440 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227 : SparsePolynomial.Poly := [([0,9,12], 1)]
theorem eval_atom0227 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7285664400 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228 : SparsePolynomial.Poly := [([0,9,13], 1)]
theorem eval_atom0228 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5561142960 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229 : SparsePolynomial.Poly := [([0,9,14], 1)]
theorem eval_atom0229 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4371383400 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230 : SparsePolynomial.Poly := [([0,9,15], 1)]
theorem eval_atom0230 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 0) * (g 9) * (g 15)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2669690640 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231 : SparsePolynomial.Poly := [([0,9,16], 1)]
theorem eval_atom0231 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 0) * (g 9) * (g 16)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2580674640 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232 : SparsePolynomial.Poly := [([0,9,17], 1)]
theorem eval_atom0232 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 0) * (g 9) * (g 17)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1270527120 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0233 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4365254400 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234 : SparsePolynomial.Poly := [([0,10,11], 1)]
theorem eval_atom0234 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8283344640 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235 : SparsePolynomial.Poly := [([0,10,12], 1)]
theorem eval_atom0235 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7677665520 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236 : SparsePolynomial.Poly := [([0,10,13], 1)]
theorem eval_atom0236 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5854253520 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237 : SparsePolynomial.Poly := [([0,10,14], 1)]
theorem eval_atom0237 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4664267880 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238 : SparsePolynomial.Poly := [([0,10,15], 1)]
theorem eval_atom0238 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 0) * (g 10) * (g 15)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2715642480 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239 : SparsePolynomial.Poly := [([0,10,16], 1)]
theorem eval_atom0239 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 0) * (g 10) * (g 16)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2454166320 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240 : SparsePolynomial.Poly := [([0,10,17], 1)]
theorem eval_atom0240 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 0) * (g 10) * (g 17)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1068439680 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241 : SparsePolynomial.Poly := [([0,11,11], 1)]
theorem eval_atom0241 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4733245440 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242 : SparsePolynomial.Poly := [([0,11,12], 1)]
theorem eval_atom0242 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8115287040 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243 : SparsePolynomial.Poly := [([0,11,13], 1)]
theorem eval_atom0243 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6077675520 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244 : SparsePolynomial.Poly := [([0,11,14], 1)]
theorem eval_atom0244 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4826851560 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245 : SparsePolynomial.Poly := [([0,11,15], 1)]
theorem eval_atom0245 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 0) * (g 11) * (g 15)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2818206720 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246 : SparsePolynomial.Poly := [([0,11,16], 1)]
theorem eval_atom0246 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 0) * (g 11) * (g 16)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2153733120 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247 : SparsePolynomial.Poly := [([0,11,17], 1)]
theorem eval_atom0247 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 0) * (g 11) * (g 17)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1093155840 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248 : SparsePolynomial.Poly := [([0,12,12], 1)]
theorem eval_atom0248 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4670668800 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249 : SparsePolynomial.Poly := [([0,12,13], 1)]
theorem eval_atom0249 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7960780800 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250 : SparsePolynomial.Poly := [([0,12,14], 1)]
theorem eval_atom0250 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8303080680 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251 : SparsePolynomial.Poly := [([0,12,15], 1)]
theorem eval_atom0251 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 0) * (g 12) * (g 15)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6976327680 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252 : SparsePolynomial.Poly := [([0,12,16], 1)]
theorem eval_atom0252 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 0) * (g 12) * (g 16)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4010227200 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253 : SparsePolynomial.Poly := [([0,12,17], 1)]
theorem eval_atom0253 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 0) * (g 12) * (g 17)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4324884480 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254 : SparsePolynomial.Poly := [([0,13,13], 1)]
theorem eval_atom0254 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3585705984 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block003 : SparsePolynomial.Poly := [([0,4,15], 1360448880), ([0,4,16], 1674024240), ([0,4,17], 703165680), ([0,5,5], 2579342400), ([0,5,6], 4516403328), ([0,5,7], 4367547360), ([0,5,8], 4567144800), ([0,5,9], 4768422240), ([0,5,10], 4983085920), ([0,5,11], 5216364000), ([0,5,12], 5941555200), ([0,5,13], 4162226220), ([0,5,14], 3238888680), ([0,5,15], 1754614980), ([0,5,16], 2027377620), ([0,5,17], 1015706340), ([0,6,6], 2842228800), ([0,6,7], 5214287808), ([0,6,8], 5033727840), ([0,6,9], 5249197920), ([0,6,10], 5464668000), ([0,6,11], 5698752480), ([0,6,12], 6261373440), ([0,6,13], 4589920620), ([0,6,14], 3503549160), ([0,6,15], 2071308420), ([0,6,16], 2269801620), ([0,6,17], 1183860900), ([0,7,7], 3277226880), ([0,7,8], 6038429568), ([0,7,9], 5672303040), ([0,7,10], 5875999680), ([0,7,11], 6098310720), ([0,7,12], 6581191680), ([0,7,13], 4932461160), ([0,7,14], 3768209640), ([0,7,15], 2323360440), ([0,7,16], 2465452440), ([0,7,17], 1323110520), ([0,8,8], 3666370560), ([0,8,9], 6875078400), ([0,8,10], 6343352832), ([0,8,11], 6498405120), ([0,8,12], 6913818240), ([0,8,13], 5270770560), ([0,8,14], 4122528360), ([0,8,15], 2586806400), ([0,8,16], 2610257280), ([0,8,17], 1426124160), ([0,9,9], 4060320000), ([0,9,10], 7582617600), ([0,9,11], 7116061440), ([0,9,12], 7285664400), ([0,9,13], 5561142960), ([0,9,14], 4371383400), ([0,9,15], 2669690640), ([0,9,16], 2580674640), ([0,9,17], 1270527120), ([0,10,10], 4365254400), ([0,10,11], 8283344640), ([0,10,12], 7677665520), ([0,10,13], 5854253520), ([0,10,14], 4664267880), ([0,10,15], 2715642480), ([0,10,16], 2454166320), ([0,10,17], 1068439680), ([0,11,11], 4733245440), ([0,11,12], 8115287040), ([0,11,13], 6077675520), ([0,11,14], 4826851560), ([0,11,15], 2818206720), ([0,11,16], 2153733120), ([0,11,17], 1093155840), ([0,12,12], 4670668800), ([0,12,13], 7960780800), ([0,12,14], 8303080680), ([0,12,15], 6976327680), ([0,12,16], 4010227200), ([0,12,17], 4324884480), ([0,13,13], 3585705984)]
theorem block003_data : block003 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1360448880 : Int) atom0175) (SparsePolynomial.scale (1674024240 : Int) atom0176)) (SparsePolynomial.merge (SparsePolynomial.scale (703165680 : Int) atom0177) (SparsePolynomial.merge (SparsePolynomial.scale (2579342400 : Int) atom0178) (SparsePolynomial.scale (4516403328 : Int) atom0179)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4367547360 : Int) atom0180) (SparsePolynomial.scale (4567144800 : Int) atom0181)) (SparsePolynomial.merge (SparsePolynomial.scale (4768422240 : Int) atom0182) (SparsePolynomial.merge (SparsePolynomial.scale (4983085920 : Int) atom0183) (SparsePolynomial.scale (5216364000 : Int) atom0184))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5941555200 : Int) atom0185) (SparsePolynomial.scale (4162226220 : Int) atom0186)) (SparsePolynomial.merge (SparsePolynomial.scale (3238888680 : Int) atom0187) (SparsePolynomial.merge (SparsePolynomial.scale (1754614980 : Int) atom0188) (SparsePolynomial.scale (2027377620 : Int) atom0189)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1015706340 : Int) atom0190) (SparsePolynomial.scale (2842228800 : Int) atom0191)) (SparsePolynomial.merge (SparsePolynomial.scale (5214287808 : Int) atom0192) (SparsePolynomial.merge (SparsePolynomial.scale (5033727840 : Int) atom0193) (SparsePolynomial.scale (5249197920 : Int) atom0194)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5464668000 : Int) atom0195) (SparsePolynomial.scale (5698752480 : Int) atom0196)) (SparsePolynomial.merge (SparsePolynomial.scale (6261373440 : Int) atom0197) (SparsePolynomial.merge (SparsePolynomial.scale (4589920620 : Int) atom0198) (SparsePolynomial.scale (3503549160 : Int) atom0199)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2071308420 : Int) atom0200) (SparsePolynomial.scale (2269801620 : Int) atom0201)) (SparsePolynomial.merge (SparsePolynomial.scale (1183860900 : Int) atom0202) (SparsePolynomial.merge (SparsePolynomial.scale (3277226880 : Int) atom0203) (SparsePolynomial.scale (6038429568 : Int) atom0204))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5672303040 : Int) atom0205) (SparsePolynomial.scale (5875999680 : Int) atom0206)) (SparsePolynomial.merge (SparsePolynomial.scale (6098310720 : Int) atom0207) (SparsePolynomial.merge (SparsePolynomial.scale (6581191680 : Int) atom0208) (SparsePolynomial.scale (4932461160 : Int) atom0209)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3768209640 : Int) atom0210) (SparsePolynomial.scale (2323360440 : Int) atom0211)) (SparsePolynomial.merge (SparsePolynomial.scale (2465452440 : Int) atom0212) (SparsePolynomial.merge (SparsePolynomial.scale (1323110520 : Int) atom0213) (SparsePolynomial.scale (3666370560 : Int) atom0214))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6875078400 : Int) atom0215) (SparsePolynomial.scale (6343352832 : Int) atom0216)) (SparsePolynomial.merge (SparsePolynomial.scale (6498405120 : Int) atom0217) (SparsePolynomial.merge (SparsePolynomial.scale (6913818240 : Int) atom0218) (SparsePolynomial.scale (5270770560 : Int) atom0219)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4122528360 : Int) atom0220) (SparsePolynomial.scale (2586806400 : Int) atom0221)) (SparsePolynomial.merge (SparsePolynomial.scale (2610257280 : Int) atom0222) (SparsePolynomial.merge (SparsePolynomial.scale (1426124160 : Int) atom0223) (SparsePolynomial.scale (4060320000 : Int) atom0224))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7582617600 : Int) atom0225) (SparsePolynomial.scale (7116061440 : Int) atom0226)) (SparsePolynomial.merge (SparsePolynomial.scale (7285664400 : Int) atom0227) (SparsePolynomial.merge (SparsePolynomial.scale (5561142960 : Int) atom0228) (SparsePolynomial.scale (4371383400 : Int) atom0229)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2669690640 : Int) atom0230) (SparsePolynomial.scale (2580674640 : Int) atom0231)) (SparsePolynomial.merge (SparsePolynomial.scale (1270527120 : Int) atom0232) (SparsePolynomial.merge (SparsePolynomial.scale (4365254400 : Int) atom0233) (SparsePolynomial.scale (8283344640 : Int) atom0234)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7677665520 : Int) atom0235) (SparsePolynomial.scale (5854253520 : Int) atom0236)) (SparsePolynomial.merge (SparsePolynomial.scale (4664267880 : Int) atom0237) (SparsePolynomial.merge (SparsePolynomial.scale (2715642480 : Int) atom0238) (SparsePolynomial.scale (2454166320 : Int) atom0239)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1068439680 : Int) atom0240) (SparsePolynomial.scale (4733245440 : Int) atom0241)) (SparsePolynomial.merge (SparsePolynomial.scale (8115287040 : Int) atom0242) (SparsePolynomial.merge (SparsePolynomial.scale (6077675520 : Int) atom0243) (SparsePolynomial.scale (4826851560 : Int) atom0244))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2818206720 : Int) atom0245) (SparsePolynomial.scale (2153733120 : Int) atom0246)) (SparsePolynomial.merge (SparsePolynomial.scale (1093155840 : Int) atom0247) (SparsePolynomial.merge (SparsePolynomial.scale (4670668800 : Int) atom0248) (SparsePolynomial.scale (7960780800 : Int) atom0249)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8303080680 : Int) atom0250) (SparsePolynomial.scale (6976327680 : Int) atom0251)) (SparsePolynomial.merge (SparsePolynomial.scale (4010227200 : Int) atom0252) (SparsePolynomial.merge (SparsePolynomial.scale (4324884480 : Int) atom0253) (SparsePolynomial.scale (3585705984 : Int) atom0254)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block003 := by
  rw [block003_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0175_nonneg g hg hA hB) (atom0176_nonneg g hg hA hB)) (add_nonneg (atom0177_nonneg g hg hA hB) (add_nonneg (atom0178_nonneg g hg hA hB) (atom0179_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0180_nonneg g hg hA hB) (atom0181_nonneg g hg hA hB)) (add_nonneg (atom0182_nonneg g hg hA hB) (add_nonneg (atom0183_nonneg g hg hA hB) (atom0184_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0185_nonneg g hg hA hB) (atom0186_nonneg g hg hA hB)) (add_nonneg (atom0187_nonneg g hg hA hB) (add_nonneg (atom0188_nonneg g hg hA hB) (atom0189_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0190_nonneg g hg hA hB) (atom0191_nonneg g hg hA hB)) (add_nonneg (atom0192_nonneg g hg hA hB) (add_nonneg (atom0193_nonneg g hg hA hB) (atom0194_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0195_nonneg g hg hA hB) (atom0196_nonneg g hg hA hB)) (add_nonneg (atom0197_nonneg g hg hA hB) (add_nonneg (atom0198_nonneg g hg hA hB) (atom0199_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0200_nonneg g hg hA hB) (atom0201_nonneg g hg hA hB)) (add_nonneg (atom0202_nonneg g hg hA hB) (add_nonneg (atom0203_nonneg g hg hA hB) (atom0204_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0205_nonneg g hg hA hB) (atom0206_nonneg g hg hA hB)) (add_nonneg (atom0207_nonneg g hg hA hB) (add_nonneg (atom0208_nonneg g hg hA hB) (atom0209_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0210_nonneg g hg hA hB) (atom0211_nonneg g hg hA hB)) (add_nonneg (atom0212_nonneg g hg hA hB) (add_nonneg (atom0213_nonneg g hg hA hB) (atom0214_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0215_nonneg g hg hA hB) (atom0216_nonneg g hg hA hB)) (add_nonneg (atom0217_nonneg g hg hA hB) (add_nonneg (atom0218_nonneg g hg hA hB) (atom0219_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0220_nonneg g hg hA hB) (atom0221_nonneg g hg hA hB)) (add_nonneg (atom0222_nonneg g hg hA hB) (add_nonneg (atom0223_nonneg g hg hA hB) (atom0224_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0225_nonneg g hg hA hB) (atom0226_nonneg g hg hA hB)) (add_nonneg (atom0227_nonneg g hg hA hB) (add_nonneg (atom0228_nonneg g hg hA hB) (atom0229_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0230_nonneg g hg hA hB) (atom0231_nonneg g hg hA hB)) (add_nonneg (atom0232_nonneg g hg hA hB) (add_nonneg (atom0233_nonneg g hg hA hB) (atom0234_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0235_nonneg g hg hA hB) (atom0236_nonneg g hg hA hB)) (add_nonneg (atom0237_nonneg g hg hA hB) (add_nonneg (atom0238_nonneg g hg hA hB) (atom0239_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0240_nonneg g hg hA hB) (atom0241_nonneg g hg hA hB)) (add_nonneg (atom0242_nonneg g hg hA hB) (add_nonneg (atom0243_nonneg g hg hA hB) (atom0244_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0245_nonneg g hg hA hB) (atom0246_nonneg g hg hA hB)) (add_nonneg (atom0247_nonneg g hg hA hB) (add_nonneg (atom0248_nonneg g hg hA hB) (atom0249_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0250_nonneg g hg hA hB) (atom0251_nonneg g hg hA hB)) (add_nonneg (atom0252_nonneg g hg hA hB) (add_nonneg (atom0253_nonneg g hg hA hB) (atom0254_nonneg g hg hA hB))))))))

end APPT.Finite18
