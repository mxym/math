import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0289 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0289 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (162146671948800 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290 : SparsePolynomial.Poly := [([0,3,15], 1)]
theorem eval_atom0290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0290 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165208450176000 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291 : SparsePolynomial.Poly := [([0,3,16], 1)]
theorem eval_atom0291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0291 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (168270228403200 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292 : SparsePolynomial.Poly := [([0,3,17], 1)]
theorem eval_atom0292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0292 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171332006630400 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293 : SparsePolynomial.Poly := [([0,3,18], 1)]
theorem eval_atom0293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0293 = ((g 0) * (g 3) * (g 18)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (194231556288000 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294 : SparsePolynomial.Poly := [([0,3,19], 1)]
theorem eval_atom0294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0294 = ((g 0) * (g 3) * (g 19)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121344224601600 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295 : SparsePolynomial.Poly := [([0,3,20], 1)]
theorem eval_atom0295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0295 = ((g 0) * (g 3) * (g 20)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98593511385600 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296 : SparsePolynomial.Poly := [([0,3,21], 1)]
theorem eval_atom0296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0296 = ((g 0) * (g 3) * (g 21)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28810482624000 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297 : SparsePolynomial.Poly := [([0,3,22], 1)]
theorem eval_atom0297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0297 = ((g 0) * (g 3) * (g 22)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38762067254400 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298 : SparsePolynomial.Poly := [([0,3,23], 1)]
theorem eval_atom0298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0298 = ((g 0) * (g 3) * (g 23)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4273732108800 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0299 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72859948358400 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0300 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134698516442424 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0301 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136589328691200 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0302 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140671699660800 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0303 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144754070630400 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0304 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148836441600000 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0305 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152918812569600 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0306 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (161648510303808 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0307 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (215408764568448 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0308 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (196002793324800 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0309 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (169248296448000 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310 : SparsePolynomial.Poly := [([0,4,15], 1)]
theorem eval_atom0310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0310 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (173330667417600 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311 : SparsePolynomial.Poly := [([0,4,16], 1)]
theorem eval_atom0311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0311 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177413038387200 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312 : SparsePolynomial.Poly := [([0,4,17], 1)]
theorem eval_atom0312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0312 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (182657267856000 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313 : SparsePolynomial.Poly := [([0,4,18], 1)]
theorem eval_atom0313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0313 = ((g 0) * (g 4) * (g 18)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (204644791612800 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314 : SparsePolynomial.Poly := [([0,4,19], 1)]
theorem eval_atom0314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0314 = ((g 0) * (g 4) * (g 19)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (139707504493200 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315 : SparsePolynomial.Poly := [([0,4,20], 1)]
theorem eval_atom0315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0315 = ((g 0) * (g 4) * (g 20)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (106646444780400 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316 : SparsePolynomial.Poly := [([0,4,21], 1)]
theorem eval_atom0316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0316 = ((g 0) * (g 4) * (g 21)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47333592558000 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317 : SparsePolynomial.Poly := [([0,4,22], 1)]
theorem eval_atom0317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0317 = ((g 0) * (g 4) * (g 22)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57134810502000 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318 : SparsePolynomial.Poly := [([0,4,23], 1)]
theorem eval_atom0318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0318 = ((g 0) * (g 4) * (g 23)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22496108670000 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0319 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82684750579200 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0320 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148625354906424 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0321 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148356622442424 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0322 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (154227963861576 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0323 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158423328078444 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0324 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158481345814308 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0325 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165688356575808 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326 : SparsePolynomial.Poly := [([0,5,12], 1)]
theorem eval_atom0326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0326 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220469203582848 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327 : SparsePolynomial.Poly := [([0,5,13], 1)]
theorem eval_atom0327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0327 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (202083825081600 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328 : SparsePolynomial.Poly := [([0,5,14], 1)]
theorem eval_atom0328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0328 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (176349920947200 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329 : SparsePolynomial.Poly := [([0,5,15], 1)]
theorem eval_atom0329 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0329 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0329_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (181637319427200 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330 : SparsePolynomial.Poly := [([0,5,16], 1)]
theorem eval_atom0330 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0330 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0330_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189880345468800 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331 : SparsePolynomial.Poly := [([0,5,17], 1)]
theorem eval_atom0331 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0331 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0331_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (195640186896000 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332 : SparsePolynomial.Poly := [([0,5,18], 1)]
theorem eval_atom0332 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0332 = ((g 0) * (g 5) * (g 18)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0332_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (216778750372800 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333 : SparsePolynomial.Poly := [([0,5,19], 1)]
theorem eval_atom0333 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0333 = ((g 0) * (g 5) * (g 19)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0333_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158226313291200 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334 : SparsePolynomial.Poly := [([0,5,20], 1)]
theorem eval_atom0334 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0334 = ((g 0) * (g 5) * (g 20)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0334_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130583902680000 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335 : SparsePolynomial.Poly := [([0,5,21], 1)]
theorem eval_atom0335 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0335 = ((g 0) * (g 5) * (g 21)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0335_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75892956955200 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336 : SparsePolynomial.Poly := [([0,5,22], 1)]
theorem eval_atom0336 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0336 = ((g 0) * (g 5) * (g 22)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0336_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81891667368000 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337 : SparsePolynomial.Poly := [([0,5,23], 1)]
theorem eval_atom0337 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0337 = ((g 0) * (g 5) * (g 23)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0337_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53774798616000 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0338 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0338 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0338_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100400811033600 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0339 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177142415936640 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0340 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0340 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0340_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (167536677369600 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0341 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0341 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0341_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171625729842468 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0342 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0342 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0342_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (174036270802284 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0343 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0343 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0343_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (179411685885432 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344 : SparsePolynomial.Poly := [([0,6,12], 1)]
theorem eval_atom0344 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0344 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0344_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (227754227230992 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345 : SparsePolynomial.Poly := [([0,6,13], 1)]
theorem eval_atom0345 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0345 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0345_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (212591933215200 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346 : SparsePolynomial.Poly := [([0,6,14], 1)]
theorem eval_atom0346 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0346 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0346_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (190999679270400 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347 : SparsePolynomial.Poly := [([0,6,15], 1)]
theorem eval_atom0347 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0347 = ((g 0) * (g 6) * (g 15)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0347_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (196547541523200 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348 : SparsePolynomial.Poly := [([0,6,16], 1)]
theorem eval_atom0348 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0348 = ((g 0) * (g 6) * (g 16)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0348_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205051031337600 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349 : SparsePolynomial.Poly := [([0,6,17], 1)]
theorem eval_atom0349 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0349 = ((g 0) * (g 6) * (g 17)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0349_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211071336537600 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350 : SparsePolynomial.Poly := [([0,6,18], 1)]
theorem eval_atom0350 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0350 = ((g 0) * (g 6) * (g 18)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0350_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229282538284800 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351 : SparsePolynomial.Poly := [([0,6,19], 1)]
theorem eval_atom0351 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0351 = ((g 0) * (g 6) * (g 19)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0351_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (169646965488000 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352 : SparsePolynomial.Poly := [([0,6,20], 1)]
theorem eval_atom0352 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0352 = ((g 0) * (g 6) * (g 20)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0352_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134261101497600 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353 : SparsePolynomial.Poly := [([0,6,21], 1)]
theorem eval_atom0353 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0353 = ((g 0) * (g 6) * (g 21)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0353_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78771686716800 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354 : SparsePolynomial.Poly := [([0,6,22], 1)]
theorem eval_atom0354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0354 = ((g 0) * (g 6) * (g 22)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89313301526400 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355 : SparsePolynomial.Poly := [([0,6,23], 1)]
theorem eval_atom0355 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0355 = ((g 0) * (g 6) * (g 23)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0355_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55414996560000 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0356 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0356 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0356_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112758960652800 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0357 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0357 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0357_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207122327744640 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358 : SparsePolynomial.Poly := [([0,7,9], 1)]
theorem eval_atom0358 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0358 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0358_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (186386366252196 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359 : SparsePolynomial.Poly := [([0,7,10], 1)]
theorem eval_atom0359 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0359 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0359_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (187147461941484 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360 : SparsePolynomial.Poly := [([0,7,11], 1)]
theorem eval_atom0360 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0360 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0360_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193043804570232 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361 : SparsePolynomial.Poly := [([0,7,12], 1)]
theorem eval_atom0361 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0361 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0361_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241907273461392 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362 : SparsePolynomial.Poly := [([0,7,13], 1)]
theorem eval_atom0362 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0362 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0362_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (226750295032800 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363 : SparsePolynomial.Poly := [([0,7,14], 1)]
theorem eval_atom0363 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0363 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0363_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205163356675200 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364 : SparsePolynomial.Poly := [([0,7,15], 1)]
theorem eval_atom0364 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0364 = ((g 0) * (g 7) * (g 15)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0364_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (210716534515200 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365 : SparsePolynomial.Poly := [([0,7,16], 1)]
theorem eval_atom0365 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0365 = ((g 0) * (g 7) * (g 16)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0365_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (219225339916800 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366 : SparsePolynomial.Poly := [([0,7,17], 1)]
theorem eval_atom0366 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0366 = ((g 0) * (g 7) * (g 17)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0366_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225250960704000 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367 : SparsePolynomial.Poly := [([0,7,18], 1)]
theorem eval_atom0367 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0367 = ((g 0) * (g 7) * (g 18)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0367_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (243279070003200 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368 : SparsePolynomial.Poly := [([0,7,19], 1)]
theorem eval_atom0368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0368 = ((g 0) * (g 7) * (g 19)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (183271996723200 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block006 : SparsePolynomial.Poly := [([0,3,14], 162146671948800), ([0,3,15], 165208450176000), ([0,3,16], 168270228403200), ([0,3,17], 171332006630400), ([0,3,18], 194231556288000), ([0,3,19], 121344224601600), ([0,3,20], 98593511385600), ([0,3,21], 28810482624000), ([0,3,22], 38762067254400), ([0,3,23], 4273732108800), ([0,4,4], 72859948358400), ([0,4,5], 134698516442424), ([0,4,6], 136589328691200), ([0,4,7], 140671699660800), ([0,4,8], 144754070630400), ([0,4,9], 148836441600000), ([0,4,10], 152918812569600), ([0,4,11], 161648510303808), ([0,4,12], 215408764568448), ([0,4,13], 196002793324800), ([0,4,14], 169248296448000), ([0,4,15], 173330667417600), ([0,4,16], 177413038387200), ([0,4,17], 182657267856000), ([0,4,18], 204644791612800), ([0,4,19], 139707504493200), ([0,4,20], 106646444780400), ([0,4,21], 47333592558000), ([0,4,22], 57134810502000), ([0,4,23], 22496108670000), ([0,5,5], 82684750579200), ([0,5,6], 148625354906424), ([0,5,7], 148356622442424), ([0,5,8], 154227963861576), ([0,5,9], 158423328078444), ([0,5,10], 158481345814308), ([0,5,11], 165688356575808), ([0,5,12], 220469203582848), ([0,5,13], 202083825081600), ([0,5,14], 176349920947200), ([0,5,15], 181637319427200), ([0,5,16], 189880345468800), ([0,5,17], 195640186896000), ([0,5,18], 216778750372800), ([0,5,19], 158226313291200), ([0,5,20], 130583902680000), ([0,5,21], 75892956955200), ([0,5,22], 81891667368000), ([0,5,23], 53774798616000), ([0,6,6], 100400811033600), ([0,6,7], 177142415936640), ([0,6,8], 167536677369600), ([0,6,9], 171625729842468), ([0,6,10], 174036270802284), ([0,6,11], 179411685885432), ([0,6,12], 227754227230992), ([0,6,13], 212591933215200), ([0,6,14], 190999679270400), ([0,6,15], 196547541523200), ([0,6,16], 205051031337600), ([0,6,17], 211071336537600), ([0,6,18], 229282538284800), ([0,6,19], 169646965488000), ([0,6,20], 134261101497600), ([0,6,21], 78771686716800), ([0,6,22], 89313301526400), ([0,6,23], 55414996560000), ([0,7,7], 112758960652800), ([0,7,8], 207122327744640), ([0,7,9], 186386366252196), ([0,7,10], 187147461941484), ([0,7,11], 193043804570232), ([0,7,12], 241907273461392), ([0,7,13], 226750295032800), ([0,7,14], 205163356675200), ([0,7,15], 210716534515200), ([0,7,16], 219225339916800), ([0,7,17], 225250960704000), ([0,7,18], 243279070003200), ([0,7,19], 183271996723200)]
theorem block006_data : block006 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (162146671948800 : Int) atom0289) (SparsePolynomial.scale (165208450176000 : Int) atom0290)) (SparsePolynomial.merge (SparsePolynomial.scale (168270228403200 : Int) atom0291) (SparsePolynomial.merge (SparsePolynomial.scale (171332006630400 : Int) atom0292) (SparsePolynomial.scale (194231556288000 : Int) atom0293)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (121344224601600 : Int) atom0294) (SparsePolynomial.scale (98593511385600 : Int) atom0295)) (SparsePolynomial.merge (SparsePolynomial.scale (28810482624000 : Int) atom0296) (SparsePolynomial.merge (SparsePolynomial.scale (38762067254400 : Int) atom0297) (SparsePolynomial.scale (4273732108800 : Int) atom0298))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (72859948358400 : Int) atom0299) (SparsePolynomial.scale (134698516442424 : Int) atom0300)) (SparsePolynomial.merge (SparsePolynomial.scale (136589328691200 : Int) atom0301) (SparsePolynomial.merge (SparsePolynomial.scale (140671699660800 : Int) atom0302) (SparsePolynomial.scale (144754070630400 : Int) atom0303)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (148836441600000 : Int) atom0304) (SparsePolynomial.scale (152918812569600 : Int) atom0305)) (SparsePolynomial.merge (SparsePolynomial.scale (161648510303808 : Int) atom0306) (SparsePolynomial.merge (SparsePolynomial.scale (215408764568448 : Int) atom0307) (SparsePolynomial.scale (196002793324800 : Int) atom0308)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (169248296448000 : Int) atom0309) (SparsePolynomial.scale (173330667417600 : Int) atom0310)) (SparsePolynomial.merge (SparsePolynomial.scale (177413038387200 : Int) atom0311) (SparsePolynomial.merge (SparsePolynomial.scale (182657267856000 : Int) atom0312) (SparsePolynomial.scale (204644791612800 : Int) atom0313)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (139707504493200 : Int) atom0314) (SparsePolynomial.scale (106646444780400 : Int) atom0315)) (SparsePolynomial.merge (SparsePolynomial.scale (47333592558000 : Int) atom0316) (SparsePolynomial.merge (SparsePolynomial.scale (57134810502000 : Int) atom0317) (SparsePolynomial.scale (22496108670000 : Int) atom0318))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (82684750579200 : Int) atom0319) (SparsePolynomial.scale (148625354906424 : Int) atom0320)) (SparsePolynomial.merge (SparsePolynomial.scale (148356622442424 : Int) atom0321) (SparsePolynomial.merge (SparsePolynomial.scale (154227963861576 : Int) atom0322) (SparsePolynomial.scale (158423328078444 : Int) atom0323)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (158481345814308 : Int) atom0324) (SparsePolynomial.scale (165688356575808 : Int) atom0325)) (SparsePolynomial.merge (SparsePolynomial.scale (220469203582848 : Int) atom0326) (SparsePolynomial.merge (SparsePolynomial.scale (202083825081600 : Int) atom0327) (SparsePolynomial.scale (176349920947200 : Int) atom0328))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (181637319427200 : Int) atom0329) (SparsePolynomial.scale (189880345468800 : Int) atom0330)) (SparsePolynomial.merge (SparsePolynomial.scale (195640186896000 : Int) atom0331) (SparsePolynomial.merge (SparsePolynomial.scale (216778750372800 : Int) atom0332) (SparsePolynomial.scale (158226313291200 : Int) atom0333)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (130583902680000 : Int) atom0334) (SparsePolynomial.scale (75892956955200 : Int) atom0335)) (SparsePolynomial.merge (SparsePolynomial.scale (81891667368000 : Int) atom0336) (SparsePolynomial.merge (SparsePolynomial.scale (53774798616000 : Int) atom0337) (SparsePolynomial.scale (100400811033600 : Int) atom0338))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (177142415936640 : Int) atom0339) (SparsePolynomial.scale (167536677369600 : Int) atom0340)) (SparsePolynomial.merge (SparsePolynomial.scale (171625729842468 : Int) atom0341) (SparsePolynomial.merge (SparsePolynomial.scale (174036270802284 : Int) atom0342) (SparsePolynomial.scale (179411685885432 : Int) atom0343)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (227754227230992 : Int) atom0344) (SparsePolynomial.scale (212591933215200 : Int) atom0345)) (SparsePolynomial.merge (SparsePolynomial.scale (190999679270400 : Int) atom0346) (SparsePolynomial.merge (SparsePolynomial.scale (196547541523200 : Int) atom0347) (SparsePolynomial.scale (205051031337600 : Int) atom0348)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (211071336537600 : Int) atom0349) (SparsePolynomial.scale (229282538284800 : Int) atom0350)) (SparsePolynomial.merge (SparsePolynomial.scale (169646965488000 : Int) atom0351) (SparsePolynomial.merge (SparsePolynomial.scale (134261101497600 : Int) atom0352) (SparsePolynomial.scale (78771686716800 : Int) atom0353)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (89313301526400 : Int) atom0354) (SparsePolynomial.scale (55414996560000 : Int) atom0355)) (SparsePolynomial.merge (SparsePolynomial.scale (112758960652800 : Int) atom0356) (SparsePolynomial.merge (SparsePolynomial.scale (207122327744640 : Int) atom0357) (SparsePolynomial.scale (186386366252196 : Int) atom0358))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (187147461941484 : Int) atom0359) (SparsePolynomial.scale (193043804570232 : Int) atom0360)) (SparsePolynomial.merge (SparsePolynomial.scale (241907273461392 : Int) atom0361) (SparsePolynomial.merge (SparsePolynomial.scale (226750295032800 : Int) atom0362) (SparsePolynomial.scale (205163356675200 : Int) atom0363)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (210716534515200 : Int) atom0364) (SparsePolynomial.scale (219225339916800 : Int) atom0365)) (SparsePolynomial.merge (SparsePolynomial.scale (225250960704000 : Int) atom0366) (SparsePolynomial.merge (SparsePolynomial.scale (243279070003200 : Int) atom0367) (SparsePolynomial.scale (183271996723200 : Int) atom0368)))))))) := by decide +kernel
theorem block006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block006 := by
  rw [block006_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0289_nonneg g hg hA hB) (atom0290_nonneg g hg hA hB)) (add_nonneg (atom0291_nonneg g hg hA hB) (add_nonneg (atom0292_nonneg g hg hA hB) (atom0293_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0294_nonneg g hg hA hB) (atom0295_nonneg g hg hA hB)) (add_nonneg (atom0296_nonneg g hg hA hB) (add_nonneg (atom0297_nonneg g hg hA hB) (atom0298_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0299_nonneg g hg hA hB) (atom0300_nonneg g hg hA hB)) (add_nonneg (atom0301_nonneg g hg hA hB) (add_nonneg (atom0302_nonneg g hg hA hB) (atom0303_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0304_nonneg g hg hA hB) (atom0305_nonneg g hg hA hB)) (add_nonneg (atom0306_nonneg g hg hA hB) (add_nonneg (atom0307_nonneg g hg hA hB) (atom0308_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0309_nonneg g hg hA hB) (atom0310_nonneg g hg hA hB)) (add_nonneg (atom0311_nonneg g hg hA hB) (add_nonneg (atom0312_nonneg g hg hA hB) (atom0313_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0314_nonneg g hg hA hB) (atom0315_nonneg g hg hA hB)) (add_nonneg (atom0316_nonneg g hg hA hB) (add_nonneg (atom0317_nonneg g hg hA hB) (atom0318_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0319_nonneg g hg hA hB) (atom0320_nonneg g hg hA hB)) (add_nonneg (atom0321_nonneg g hg hA hB) (add_nonneg (atom0322_nonneg g hg hA hB) (atom0323_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0324_nonneg g hg hA hB) (atom0325_nonneg g hg hA hB)) (add_nonneg (atom0326_nonneg g hg hA hB) (add_nonneg (atom0327_nonneg g hg hA hB) (atom0328_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0329_nonneg g hg hA hB) (atom0330_nonneg g hg hA hB)) (add_nonneg (atom0331_nonneg g hg hA hB) (add_nonneg (atom0332_nonneg g hg hA hB) (atom0333_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0334_nonneg g hg hA hB) (atom0335_nonneg g hg hA hB)) (add_nonneg (atom0336_nonneg g hg hA hB) (add_nonneg (atom0337_nonneg g hg hA hB) (atom0338_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0339_nonneg g hg hA hB) (atom0340_nonneg g hg hA hB)) (add_nonneg (atom0341_nonneg g hg hA hB) (add_nonneg (atom0342_nonneg g hg hA hB) (atom0343_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0344_nonneg g hg hA hB) (atom0345_nonneg g hg hA hB)) (add_nonneg (atom0346_nonneg g hg hA hB) (add_nonneg (atom0347_nonneg g hg hA hB) (atom0348_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0349_nonneg g hg hA hB) (atom0350_nonneg g hg hA hB)) (add_nonneg (atom0351_nonneg g hg hA hB) (add_nonneg (atom0352_nonneg g hg hA hB) (atom0353_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0354_nonneg g hg hA hB) (atom0355_nonneg g hg hA hB)) (add_nonneg (atom0356_nonneg g hg hA hB) (add_nonneg (atom0357_nonneg g hg hA hB) (atom0358_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0359_nonneg g hg hA hB) (atom0360_nonneg g hg hA hB)) (add_nonneg (atom0361_nonneg g hg hA hB) (add_nonneg (atom0362_nonneg g hg hA hB) (atom0363_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0364_nonneg g hg hA hB) (atom0365_nonneg g hg hA hB)) (add_nonneg (atom0366_nonneg g hg hA hB) (add_nonneg (atom0367_nonneg g hg hA hB) (atom0368_nonneg g hg hA hB))))))))

end APPT.Finite24
