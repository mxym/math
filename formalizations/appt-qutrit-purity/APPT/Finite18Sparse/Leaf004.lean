import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0255 : SparsePolynomial.Poly := [([0,13,14], 1)]
theorem eval_atom0255 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0255 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0255_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6818918400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256 : SparsePolynomial.Poly := [([0,13,15], 1)]
theorem eval_atom0256 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0256 = ((g 0) * (g 13) * (g 15)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0256_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7265341440 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257 : SparsePolynomial.Poly := [([0,13,16], 1)]
theorem eval_atom0257 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0257 = ((g 0) * (g 13) * (g 16)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0257_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4226019840 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258 : SparsePolynomial.Poly := [([0,13,17], 1)]
theorem eval_atom0258 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0258 = ((g 0) * (g 13) * (g 17)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0258_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4714536960 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259 : SparsePolynomial.Poly := [([0,14,14], 1)]
theorem eval_atom0259 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0259 = ((g 0) * (g 14) * (g 14)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0259_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3528806400 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260 : SparsePolynomial.Poly := [([0,14,15], 1)]
theorem eval_atom0260 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0260 = ((g 0) * (g 14) * (g 15)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0260_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7554355200 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261 : SparsePolynomial.Poly := [([0,14,16], 1)]
theorem eval_atom0261 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0261 = ((g 0) * (g 14) * (g 16)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0261_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4318272000 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262 : SparsePolynomial.Poly := [([0,14,17], 1)]
theorem eval_atom0262 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0262 = ((g 0) * (g 14) * (g 17)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0262_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4270694400 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263 : SparsePolynomial.Poly := [([0,15,15], 1)]
theorem eval_atom0263 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0263 = ((g 0) * (g 15) * (g 15)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0263_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3921684480 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264 : SparsePolynomial.Poly := [([0,15,16], 1)]
theorem eval_atom0264 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0264 = ((g 0) * (g 15) * (g 16)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0264_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4534064640 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265 : SparsePolynomial.Poly := [([0,15,17], 1)]
theorem eval_atom0265 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0265 = ((g 0) * (g 15) * (g 17)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0265_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4660346880 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266 : SparsePolynomial.Poly := [([0,16,16], 1)]
theorem eval_atom0266 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0266 = ((g 0) * (g 16) * (g 16)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0266_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (382072320 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267 : SparsePolynomial.Poly := [([0,16,17], 1)]
theorem eval_atom0267 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0267 = ((g 0) * (g 16) * (g 17)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0267_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (589800960 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268 : SparsePolynomial.Poly := [([1,1,1], 1)]
theorem eval_atom0268 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0268 = ((g 1) * (g 1) * (g 1)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0268_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (247524480 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 1) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0269 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0269 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0269_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1200944640 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0270 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0270 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0270_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1043535360 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0271 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0271 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0271_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (886126080 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272 : SparsePolynomial.Poly := [([1,1,5], 1)]
theorem eval_atom0272 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0272 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0272_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (728716800 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0273 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0273 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0273_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (571307520 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274 : SparsePolynomial.Poly := [([1,1,7], 1)]
theorem eval_atom0274 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0274 = ((g 1) * (g 1) * (g 7)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0274_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (413898240 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275 : SparsePolynomial.Poly := [([1,1,8], 1)]
theorem eval_atom0275 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0275 = ((g 1) * (g 1) * (g 8)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0275_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (307722240 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276 : SparsePolynomial.Poly := [([1,1,9], 1)]
theorem eval_atom0276 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0276 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0276_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (141281280 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277 : SparsePolynomial.Poly := [([1,1,12], 1)]
theorem eval_atom0277 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0277 = ((g 1) * (g 1) * (g 12)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0277_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1287424320 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278 : SparsePolynomial.Poly := [([1,1,14], 1)]
theorem eval_atom0278 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0278 = ((g 1) * (g 1) * (g 14)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0278_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (222273960 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0279 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0279 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0279_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1683763200 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0280 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0280 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0280_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3153346560 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0281 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0281 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0281_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2939166720 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0282 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0282 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0282_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2724986880 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0283 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0283 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0283_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2510807040 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0284 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0284 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0284_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2296627200 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0285 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0285 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0285_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2184913920 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0286 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0286 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0286_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1952670720 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0287 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0287 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0287_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1770746880 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0288 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0288 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0288_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1727559680 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289 : SparsePolynomial.Poly := [([1,2,12], 1)]
theorem eval_atom0289 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0289 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0289_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4779048960 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290 : SparsePolynomial.Poly := [([1,2,13], 1)]
theorem eval_atom0290 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0290 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0290_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2183310080 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291 : SparsePolynomial.Poly := [([1,2,14], 1)]
theorem eval_atom0291 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0291 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0291_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4189277880 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292 : SparsePolynomial.Poly := [([1,2,15], 1)]
theorem eval_atom0292 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0292 = ((g 1) * (g 2) * (g 15)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0292_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2511192320 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293 : SparsePolynomial.Poly := [([1,2,16], 1)]
theorem eval_atom0293 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0293 = ((g 1) * (g 2) * (g 16)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0293_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2099319040 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294 : SparsePolynomial.Poly := [([1,2,17], 1)]
theorem eval_atom0294 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0294 = ((g 1) * (g 2) * (g 17)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0294_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2429898240 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0295 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0295 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0295_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1261854720 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0296 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0296 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0296_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2410168320 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0297 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0297 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0297_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2296627200 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0298 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0298 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0298_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2183086080 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0299 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0299 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0299_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2069544960 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0300 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0300 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0300_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2058470400 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0301 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0301 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0301_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1926865920 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0302 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0302 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0302_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1845580800 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0303 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0303 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0303_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1983672320 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304 : SparsePolynomial.Poly := [([1,3,12], 1)]
theorem eval_atom0304 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0304 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0304_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5055160320 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305 : SparsePolynomial.Poly := [([1,3,13], 1)]
theorem eval_atom0305 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0305 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0305_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2754241280 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306 : SparsePolynomial.Poly := [([1,3,14], 1)]
theorem eval_atom0306 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0306 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0306_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4666666680 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307 : SparsePolynomial.Poly := [([1,3,15], 1)]
theorem eval_atom0307 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0307 = ((g 1) * (g 3) * (g 15)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0307_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3396942080 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308 : SparsePolynomial.Poly := [([1,3,16], 1)]
theorem eval_atom0308 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0308 = ((g 1) * (g 3) * (g 16)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0308_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3280856320 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309 : SparsePolynomial.Poly := [([1,3,17], 1)]
theorem eval_atom0309 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0309 = ((g 1) * (g 3) * (g 17)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0309_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3164770560 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0310 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0310 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0310_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1870807680 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0311 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0311 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0311_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2693500128 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0312 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0312 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0312_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2159880000 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0313 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0313 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0313_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1899367680 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0314 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0314 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0314_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1932026880 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315 : SparsePolynomial.Poly := [([1,4,9], 1)]
theorem eval_atom0315 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0315 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0315_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1901061120 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316 : SparsePolynomial.Poly := [([1,4,10], 1)]
theorem eval_atom0316 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0316 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0316_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1920414720 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317 : SparsePolynomial.Poly := [([1,4,11], 1)]
theorem eval_atom0317 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0317 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0317_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2115733760 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318 : SparsePolynomial.Poly := [([1,4,12], 1)]
theorem eval_atom0318 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0318 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0318_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5331271680 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319 : SparsePolynomial.Poly := [([1,4,13], 1)]
theorem eval_atom0319 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0319 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0319_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3222722720 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320 : SparsePolynomial.Poly := [([1,4,14], 1)]
theorem eval_atom0320 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0320 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0320_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5144055480 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321 : SparsePolynomial.Poly := [([1,4,15], 1)]
theorem eval_atom0321 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0321 = ((g 1) * (g 4) * (g 15)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0321_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4434399200 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322 : SparsePolynomial.Poly := [([1,4,16], 1)]
theorem eval_atom0322 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0322 = ((g 1) * (g 4) * (g 16)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0322_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5008735200 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323 : SparsePolynomial.Poly := [([1,4,17], 1)]
theorem eval_atom0323 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0323 = ((g 1) * (g 4) * (g 17)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0323_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4926240480 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0324 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0324 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0324_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1948168800 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0325 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0325 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0325_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2823599808 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0326 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0326 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0326_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2301958080 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0327 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0327 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0327_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2388162240 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328 : SparsePolynomial.Poly := [([1,5,9], 1)]
theorem eval_atom0328 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0328 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0328_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2357196480 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329 : SparsePolynomial.Poly := [([1,5,10], 1)]
theorem eval_atom0329 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0329 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0329_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2403322560 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330 : SparsePolynomial.Poly := [([1,5,11], 1)]
theorem eval_atom0330 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0330 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0330_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2625414080 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331 : SparsePolynomial.Poly := [([1,5,12], 1)]
theorem eval_atom0331 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0331 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0331_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5607383040 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332 : SparsePolynomial.Poly := [([1,5,13], 1)]
theorem eval_atom0332 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0332 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0332_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3860446040 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333 : SparsePolynomial.Poly := [([1,5,14], 1)]
theorem eval_atom0333 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0333 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0333_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5621444280 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334 : SparsePolynomial.Poly := [([1,5,15], 1)]
theorem eval_atom0334 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0334 = ((g 1) * (g 5) * (g 15)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0334_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5274663560 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block004 : SparsePolynomial.Poly := [([0,13,14], 6818918400), ([0,13,15], 7265341440), ([0,13,16], 4226019840), ([0,13,17], 4714536960), ([0,14,14], 3528806400), ([0,14,15], 7554355200), ([0,14,16], 4318272000), ([0,14,17], 4270694400), ([0,15,15], 3921684480), ([0,15,16], 4534064640), ([0,15,17], 4660346880), ([0,16,16], 382072320), ([0,16,17], 589800960), ([1,1,1], 247524480), ([1,1,2], 1200944640), ([1,1,3], 1043535360), ([1,1,4], 886126080), ([1,1,5], 728716800), ([1,1,6], 571307520), ([1,1,7], 413898240), ([1,1,8], 307722240), ([1,1,9], 141281280), ([1,1,12], 1287424320), ([1,1,14], 222273960), ([1,2,2], 1683763200), ([1,2,3], 3153346560), ([1,2,4], 2939166720), ([1,2,5], 2724986880), ([1,2,6], 2510807040), ([1,2,7], 2296627200), ([1,2,8], 2184913920), ([1,2,9], 1952670720), ([1,2,10], 1770746880), ([1,2,11], 1727559680), ([1,2,12], 4779048960), ([1,2,13], 2183310080), ([1,2,14], 4189277880), ([1,2,15], 2511192320), ([1,2,16], 2099319040), ([1,2,17], 2429898240), ([1,3,3], 1261854720), ([1,3,4], 2410168320), ([1,3,5], 2296627200), ([1,3,6], 2183086080), ([1,3,7], 2069544960), ([1,3,8], 2058470400), ([1,3,9], 1926865920), ([1,3,10], 1845580800), ([1,3,11], 1983672320), ([1,3,12], 5055160320), ([1,3,13], 2754241280), ([1,3,14], 4666666680), ([1,3,15], 3396942080), ([1,3,16], 3280856320), ([1,3,17], 3164770560), ([1,4,4], 1870807680), ([1,4,5], 2693500128), ([1,4,6], 2159880000), ([1,4,7], 1899367680), ([1,4,8], 1932026880), ([1,4,9], 1901061120), ([1,4,10], 1920414720), ([1,4,11], 2115733760), ([1,4,12], 5331271680), ([1,4,13], 3222722720), ([1,4,14], 5144055480), ([1,4,15], 4434399200), ([1,4,16], 5008735200), ([1,4,17], 4926240480), ([1,5,5], 1948168800), ([1,5,6], 2823599808), ([1,5,7], 2301958080), ([1,5,8], 2388162240), ([1,5,9], 2357196480), ([1,5,10], 2403322560), ([1,5,11], 2625414080), ([1,5,12], 5607383040), ([1,5,13], 3860446040), ([1,5,14], 5621444280), ([1,5,15], 5274663560)]
theorem block004_data : block004 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6818918400 : Int) atom0255) (SparsePolynomial.scale (7265341440 : Int) atom0256)) (SparsePolynomial.merge (SparsePolynomial.scale (4226019840 : Int) atom0257) (SparsePolynomial.merge (SparsePolynomial.scale (4714536960 : Int) atom0258) (SparsePolynomial.scale (3528806400 : Int) atom0259)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7554355200 : Int) atom0260) (SparsePolynomial.scale (4318272000 : Int) atom0261)) (SparsePolynomial.merge (SparsePolynomial.scale (4270694400 : Int) atom0262) (SparsePolynomial.merge (SparsePolynomial.scale (3921684480 : Int) atom0263) (SparsePolynomial.scale (4534064640 : Int) atom0264))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4660346880 : Int) atom0265) (SparsePolynomial.scale (382072320 : Int) atom0266)) (SparsePolynomial.merge (SparsePolynomial.scale (589800960 : Int) atom0267) (SparsePolynomial.merge (SparsePolynomial.scale (247524480 : Int) atom0268) (SparsePolynomial.scale (1200944640 : Int) atom0269)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1043535360 : Int) atom0270) (SparsePolynomial.scale (886126080 : Int) atom0271)) (SparsePolynomial.merge (SparsePolynomial.scale (728716800 : Int) atom0272) (SparsePolynomial.merge (SparsePolynomial.scale (571307520 : Int) atom0273) (SparsePolynomial.scale (413898240 : Int) atom0274)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (307722240 : Int) atom0275) (SparsePolynomial.scale (141281280 : Int) atom0276)) (SparsePolynomial.merge (SparsePolynomial.scale (1287424320 : Int) atom0277) (SparsePolynomial.merge (SparsePolynomial.scale (222273960 : Int) atom0278) (SparsePolynomial.scale (1683763200 : Int) atom0279)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3153346560 : Int) atom0280) (SparsePolynomial.scale (2939166720 : Int) atom0281)) (SparsePolynomial.merge (SparsePolynomial.scale (2724986880 : Int) atom0282) (SparsePolynomial.merge (SparsePolynomial.scale (2510807040 : Int) atom0283) (SparsePolynomial.scale (2296627200 : Int) atom0284))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2184913920 : Int) atom0285) (SparsePolynomial.scale (1952670720 : Int) atom0286)) (SparsePolynomial.merge (SparsePolynomial.scale (1770746880 : Int) atom0287) (SparsePolynomial.merge (SparsePolynomial.scale (1727559680 : Int) atom0288) (SparsePolynomial.scale (4779048960 : Int) atom0289)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2183310080 : Int) atom0290) (SparsePolynomial.scale (4189277880 : Int) atom0291)) (SparsePolynomial.merge (SparsePolynomial.scale (2511192320 : Int) atom0292) (SparsePolynomial.merge (SparsePolynomial.scale (2099319040 : Int) atom0293) (SparsePolynomial.scale (2429898240 : Int) atom0294))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1261854720 : Int) atom0295) (SparsePolynomial.scale (2410168320 : Int) atom0296)) (SparsePolynomial.merge (SparsePolynomial.scale (2296627200 : Int) atom0297) (SparsePolynomial.merge (SparsePolynomial.scale (2183086080 : Int) atom0298) (SparsePolynomial.scale (2069544960 : Int) atom0299)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2058470400 : Int) atom0300) (SparsePolynomial.scale (1926865920 : Int) atom0301)) (SparsePolynomial.merge (SparsePolynomial.scale (1845580800 : Int) atom0302) (SparsePolynomial.merge (SparsePolynomial.scale (1983672320 : Int) atom0303) (SparsePolynomial.scale (5055160320 : Int) atom0304))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2754241280 : Int) atom0305) (SparsePolynomial.scale (4666666680 : Int) atom0306)) (SparsePolynomial.merge (SparsePolynomial.scale (3396942080 : Int) atom0307) (SparsePolynomial.merge (SparsePolynomial.scale (3280856320 : Int) atom0308) (SparsePolynomial.scale (3164770560 : Int) atom0309)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1870807680 : Int) atom0310) (SparsePolynomial.scale (2693500128 : Int) atom0311)) (SparsePolynomial.merge (SparsePolynomial.scale (2159880000 : Int) atom0312) (SparsePolynomial.merge (SparsePolynomial.scale (1899367680 : Int) atom0313) (SparsePolynomial.scale (1932026880 : Int) atom0314)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1901061120 : Int) atom0315) (SparsePolynomial.scale (1920414720 : Int) atom0316)) (SparsePolynomial.merge (SparsePolynomial.scale (2115733760 : Int) atom0317) (SparsePolynomial.merge (SparsePolynomial.scale (5331271680 : Int) atom0318) (SparsePolynomial.scale (3222722720 : Int) atom0319)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5144055480 : Int) atom0320) (SparsePolynomial.scale (4434399200 : Int) atom0321)) (SparsePolynomial.merge (SparsePolynomial.scale (5008735200 : Int) atom0322) (SparsePolynomial.merge (SparsePolynomial.scale (4926240480 : Int) atom0323) (SparsePolynomial.scale (1948168800 : Int) atom0324))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2823599808 : Int) atom0325) (SparsePolynomial.scale (2301958080 : Int) atom0326)) (SparsePolynomial.merge (SparsePolynomial.scale (2388162240 : Int) atom0327) (SparsePolynomial.merge (SparsePolynomial.scale (2357196480 : Int) atom0328) (SparsePolynomial.scale (2403322560 : Int) atom0329)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2625414080 : Int) atom0330) (SparsePolynomial.scale (5607383040 : Int) atom0331)) (SparsePolynomial.merge (SparsePolynomial.scale (3860446040 : Int) atom0332) (SparsePolynomial.merge (SparsePolynomial.scale (5621444280 : Int) atom0333) (SparsePolynomial.scale (5274663560 : Int) atom0334)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block004 := by
  rw [block004_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0255_nonneg g hg hA hB) (atom0256_nonneg g hg hA hB)) (add_nonneg (atom0257_nonneg g hg hA hB) (add_nonneg (atom0258_nonneg g hg hA hB) (atom0259_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0260_nonneg g hg hA hB) (atom0261_nonneg g hg hA hB)) (add_nonneg (atom0262_nonneg g hg hA hB) (add_nonneg (atom0263_nonneg g hg hA hB) (atom0264_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0265_nonneg g hg hA hB) (atom0266_nonneg g hg hA hB)) (add_nonneg (atom0267_nonneg g hg hA hB) (add_nonneg (atom0268_nonneg g hg hA hB) (atom0269_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0270_nonneg g hg hA hB) (atom0271_nonneg g hg hA hB)) (add_nonneg (atom0272_nonneg g hg hA hB) (add_nonneg (atom0273_nonneg g hg hA hB) (atom0274_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0275_nonneg g hg hA hB) (atom0276_nonneg g hg hA hB)) (add_nonneg (atom0277_nonneg g hg hA hB) (add_nonneg (atom0278_nonneg g hg hA hB) (atom0279_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0280_nonneg g hg hA hB) (atom0281_nonneg g hg hA hB)) (add_nonneg (atom0282_nonneg g hg hA hB) (add_nonneg (atom0283_nonneg g hg hA hB) (atom0284_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0285_nonneg g hg hA hB) (atom0286_nonneg g hg hA hB)) (add_nonneg (atom0287_nonneg g hg hA hB) (add_nonneg (atom0288_nonneg g hg hA hB) (atom0289_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0290_nonneg g hg hA hB) (atom0291_nonneg g hg hA hB)) (add_nonneg (atom0292_nonneg g hg hA hB) (add_nonneg (atom0293_nonneg g hg hA hB) (atom0294_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0295_nonneg g hg hA hB) (atom0296_nonneg g hg hA hB)) (add_nonneg (atom0297_nonneg g hg hA hB) (add_nonneg (atom0298_nonneg g hg hA hB) (atom0299_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0300_nonneg g hg hA hB) (atom0301_nonneg g hg hA hB)) (add_nonneg (atom0302_nonneg g hg hA hB) (add_nonneg (atom0303_nonneg g hg hA hB) (atom0304_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0305_nonneg g hg hA hB) (atom0306_nonneg g hg hA hB)) (add_nonneg (atom0307_nonneg g hg hA hB) (add_nonneg (atom0308_nonneg g hg hA hB) (atom0309_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0310_nonneg g hg hA hB) (atom0311_nonneg g hg hA hB)) (add_nonneg (atom0312_nonneg g hg hA hB) (add_nonneg (atom0313_nonneg g hg hA hB) (atom0314_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0315_nonneg g hg hA hB) (atom0316_nonneg g hg hA hB)) (add_nonneg (atom0317_nonneg g hg hA hB) (add_nonneg (atom0318_nonneg g hg hA hB) (atom0319_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0320_nonneg g hg hA hB) (atom0321_nonneg g hg hA hB)) (add_nonneg (atom0322_nonneg g hg hA hB) (add_nonneg (atom0323_nonneg g hg hA hB) (atom0324_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0325_nonneg g hg hA hB) (atom0326_nonneg g hg hA hB)) (add_nonneg (atom0327_nonneg g hg hA hB) (add_nonneg (atom0328_nonneg g hg hA hB) (atom0329_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0330_nonneg g hg hA hB) (atom0331_nonneg g hg hA hB)) (add_nonneg (atom0332_nonneg g hg hA hB) (add_nonneg (atom0333_nonneg g hg hA hB) (atom0334_nonneg g hg hA hB))))))))

end APPT.Finite18
