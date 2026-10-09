import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0256 : SparsePolynomial.Poly := [([0,6,13], 1)]
theorem eval_atom0256 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0256 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0256_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24337174377600 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257 : SparsePolynomial.Poly := [([0,6,14], 1)]
theorem eval_atom0257 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0257 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0257_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25039315123200 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258 : SparsePolynomial.Poly := [([0,6,15], 1)]
theorem eval_atom0258 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0258 = ((g 0) * (g 6) * (g 15)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0258_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29039577235200 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259 : SparsePolynomial.Poly := [([0,6,16], 1)]
theorem eval_atom0259 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0259 = ((g 0) * (g 6) * (g 16)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0259_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21558664512000 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260 : SparsePolynomial.Poly := [([0,6,17], 1)]
theorem eval_atom0260 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0260 = ((g 0) * (g 6) * (g 17)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0260_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18654996729600 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261 : SparsePolynomial.Poly := [([0,6,18], 1)]
theorem eval_atom0261 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0261 = ((g 0) * (g 6) * (g 18)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0261_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13125428870400 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262 : SparsePolynomial.Poly := [([0,6,19], 1)]
theorem eval_atom0262 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0262 = ((g 0) * (g 6) * (g 19)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0262_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13510927180800 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263 : SparsePolynomial.Poly := [([0,6,20], 1)]
theorem eval_atom0263 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0263 = ((g 0) * (g 6) * (g 20)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0263_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10819430496000 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0264 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0264 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0264_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13421582466048 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0265 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0265 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0265_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23660965873728 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266 : SparsePolynomial.Poly := [([0,7,9], 1)]
theorem eval_atom0266 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0266 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0266_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22372041369024 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267 : SparsePolynomial.Poly := [([0,7,10], 1)]
theorem eval_atom0267 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0267 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0267_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23033831975424 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268 : SparsePolynomial.Poly := [([0,7,11], 1)]
theorem eval_atom0268 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0268 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0268_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23838356994624 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269 : SparsePolynomial.Poly := [([0,7,12], 1)]
theorem eval_atom0269 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0269 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0269_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25176291029824 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270 : SparsePolynomial.Poly := [([0,7,13], 1)]
theorem eval_atom0270 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0270 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0270_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26078455353024 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271 : SparsePolynomial.Poly := [([0,7,14], 1)]
theorem eval_atom0271 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0271 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0271_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26761266690624 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272 : SparsePolynomial.Poly := [([0,7,15], 1)]
theorem eval_atom0272 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0272 = ((g 0) * (g 7) * (g 15)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0272_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30796193398176 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273 : SparsePolynomial.Poly := [([0,7,16], 1)]
theorem eval_atom0273 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0273 = ((g 0) * (g 7) * (g 16)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0273_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23976290418336 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274 : SparsePolynomial.Poly := [([0,7,17], 1)]
theorem eval_atom0274 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0274 = ((g 0) * (g 7) * (g 17)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0274_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22287869204832 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275 : SparsePolynomial.Poly := [([0,7,18], 1)]
theorem eval_atom0275 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0275 = ((g 0) * (g 7) * (g 18)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0275_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16973062270560 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276 : SparsePolynomial.Poly := [([0,7,19], 1)]
theorem eval_atom0276 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0276 = ((g 0) * (g 7) * (g 19)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0276_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16137647557920 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277 : SparsePolynomial.Poly := [([0,7,20], 1)]
theorem eval_atom0277 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0277 = ((g 0) * (g 7) * (g 20)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0277_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14405932338336 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0278 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0278 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0278_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14770003348800 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279 : SparsePolynomial.Poly := [([0,8,9], 1)]
theorem eval_atom0279 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0279 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0279_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26552598367680 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280 : SparsePolynomial.Poly := [([0,8,10], 1)]
theorem eval_atom0280 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0280 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0280_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25135035962400 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281 : SparsePolynomial.Poly := [([0,8,11], 1)]
theorem eval_atom0281 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0281 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0281_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25813436594400 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282 : SparsePolynomial.Poly := [([0,8,12], 1)]
theorem eval_atom0282 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0282 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0282_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26983204780000 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283 : SparsePolynomial.Poly := [([0,8,13], 1)]
theorem eval_atom0283 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0283 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0283_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27823998232800 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284 : SparsePolynomial.Poly := [([0,8,14], 1)]
theorem eval_atom0284 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0284 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0284_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28445438700000 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285 : SparsePolynomial.Poly := [([0,8,15], 1)]
theorem eval_atom0285 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0285 = ((g 0) * (g 8) * (g 15)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0285_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32314904294400 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286 : SparsePolynomial.Poly := [([0,8,16], 1)]
theorem eval_atom0286 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0286 = ((g 0) * (g 8) * (g 16)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0286_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25706174665500 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287 : SparsePolynomial.Poly := [([0,8,17], 1)]
theorem eval_atom0287 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0287 = ((g 0) * (g 8) * (g 17)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0287_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24255404812800 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288 : SparsePolynomial.Poly := [([0,8,18], 1)]
theorem eval_atom0288 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0288 = ((g 0) * (g 8) * (g 18)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0288_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18917112734100 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289 : SparsePolynomial.Poly := [([0,8,19], 1)]
theorem eval_atom0289 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0289 = ((g 0) * (g 8) * (g 19)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0289_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17491669568100 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290 : SparsePolynomial.Poly := [([0,8,20], 1)]
theorem eval_atom0290 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0290 = ((g 0) * (g 8) * (g 20)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0290_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15923188782900 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0291 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0291 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0291_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16313214960000 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292 : SparsePolynomial.Poly := [([0,9,10], 1)]
theorem eval_atom0292 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0292 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0292_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29540683226880 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293 : SparsePolynomial.Poly := [([0,9,11], 1)]
theorem eval_atom0293 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0293 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0293_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27605876760000 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294 : SparsePolynomial.Poly := [([0,9,12], 1)]
theorem eval_atom0294 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0294 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0294_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28779027592000 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295 : SparsePolynomial.Poly := [([0,9,13], 1)]
theorem eval_atom0295 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0295 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0295_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29516408712000 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296 : SparsePolynomial.Poly := [([0,9,14], 1)]
theorem eval_atom0296 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0296 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0296_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30034436846400 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297 : SparsePolynomial.Poly := [([0,9,15], 1)]
theorem eval_atom0297 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0297 = ((g 0) * (g 9) * (g 15)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0297_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33814866355200 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298 : SparsePolynomial.Poly := [([0,9,16], 1)]
theorem eval_atom0298 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0298 = ((g 0) * (g 9) * (g 16)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0298_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27205547783400 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299 : SparsePolynomial.Poly := [([0,9,17], 1)]
theorem eval_atom0299 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0299 = ((g 0) * (g 9) * (g 17)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0299_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26091698572800 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300 : SparsePolynomial.Poly := [([0,9,18], 1)]
theorem eval_atom0300 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0300 = ((g 0) * (g 9) * (g 18)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0300_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20444060460600 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301 : SparsePolynomial.Poly := [([0,9,19], 1)]
theorem eval_atom0301 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0301 = ((g 0) * (g 9) * (g 19)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0301_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18430701269400 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302 : SparsePolynomial.Poly := [([0,9,20], 1)]
theorem eval_atom0302 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0302 = ((g 0) * (g 9) * (g 20)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0302_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16915074334200 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0303 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0303 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0303_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17758088208000 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304 : SparsePolynomial.Poly := [([0,10,11], 1)]
theorem eval_atom0304 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0304 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0304_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32512456529280 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305 : SparsePolynomial.Poly := [([0,10,12], 1)]
theorem eval_atom0305 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0305 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0305_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30716949294080 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306 : SparsePolynomial.Poly := [([0,10,13], 1)]
theorem eval_atom0306 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0306 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0306_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31264753665600 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307 : SparsePolynomial.Poly := [([0,10,14], 1)]
theorem eval_atom0307 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0307 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0307_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31637328004800 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308 : SparsePolynomial.Poly := [([0,10,15], 1)]
theorem eval_atom0308 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0308 = ((g 0) * (g 10) * (g 15)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0308_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35314828416000 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309 : SparsePolynomial.Poly := [([0,10,16], 1)]
theorem eval_atom0309 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0309 = ((g 0) * (g 10) * (g 16)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0309_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28584761448600 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310 : SparsePolynomial.Poly := [([0,10,17], 1)]
theorem eval_atom0310 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0310 = ((g 0) * (g 10) * (g 17)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0310_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27927992332800 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311 : SparsePolynomial.Poly := [([0,10,18], 1)]
theorem eval_atom0311 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0311 = ((g 0) * (g 10) * (g 18)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0311_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21666826729800 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312 : SparsePolynomial.Poly := [([0,10,19], 1)]
theorem eval_atom0312 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0312 = ((g 0) * (g 10) * (g 19)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0312_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18956883997800 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313 : SparsePolynomial.Poly := [([0,10,20], 1)]
theorem eval_atom0313 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0313 = ((g 0) * (g 10) * (g 20)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0313_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17385443397000 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314 : SparsePolynomial.Poly := [([0,11,11], 1)]
theorem eval_atom0314 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0314 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0314_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19284988262400 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315 : SparsePolynomial.Poly := [([0,11,12], 1)]
theorem eval_atom0315 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0315 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0315_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35899040401280 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316 : SparsePolynomial.Poly := [([0,11,13], 1)]
theorem eval_atom0316 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0316 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0316_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33134812300800 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317 : SparsePolynomial.Poly := [([0,11,14], 1)]
theorem eval_atom0317 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0317 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0317_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33319891382400 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318 : SparsePolynomial.Poly := [([0,11,15], 1)]
theorem eval_atom0318 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0318 = ((g 0) * (g 11) * (g 15)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0318_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36736809580800 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319 : SparsePolynomial.Poly := [([0,11,16], 1)]
theorem eval_atom0319 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0319 = ((g 0) * (g 11) * (g 16)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0319_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29709470649600 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320 : SparsePolynomial.Poly := [([0,11,17], 1)]
theorem eval_atom0320 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0320 = ((g 0) * (g 11) * (g 17)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0320_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29218419820800 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321 : SparsePolynomial.Poly := [([0,11,18], 1)]
theorem eval_atom0321 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0321 = ((g 0) * (g 11) * (g 18)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0321_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22050818092800 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322 : SparsePolynomial.Poly := [([0,11,19], 1)]
theorem eval_atom0322 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0322 = ((g 0) * (g 11) * (g 19)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0322_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18736677388800 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323 : SparsePolynomial.Poly := [([0,11,20], 1)]
theorem eval_atom0323 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0323 = ((g 0) * (g 11) * (g 20)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0323_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16733923315200 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324 : SparsePolynomial.Poly := [([0,12,12], 1)]
theorem eval_atom0324 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0324 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0324_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21251467059200 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325 : SparsePolynomial.Poly := [([0,12,13], 1)]
theorem eval_atom0325 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0325 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0325_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39297939296000 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326 : SparsePolynomial.Poly := [([0,12,14], 1)]
theorem eval_atom0326 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0326 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0326_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35912554563200 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327 : SparsePolynomial.Poly := [([0,12,15], 1)]
theorem eval_atom0327 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0327 = ((g 0) * (g 12) * (g 15)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0327_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37646402460800 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328 : SparsePolynomial.Poly := [([0,12,16], 1)]
theorem eval_atom0328 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0328 = ((g 0) * (g 12) * (g 16)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0328_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30033533017600 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329 : SparsePolynomial.Poly := [([0,12,17], 1)]
theorem eval_atom0329 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0329 = ((g 0) * (g 12) * (g 17)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0329_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26922129315200 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330 : SparsePolynomial.Poly := [([0,12,18], 1)]
theorem eval_atom0330 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0330 = ((g 0) * (g 12) * (g 18)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0330_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18741955075200 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331 : SparsePolynomial.Poly := [([0,12,19], 1)]
theorem eval_atom0331 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0331 = ((g 0) * (g 12) * (g 19)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0331_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15709779478400 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332 : SparsePolynomial.Poly := [([0,12,20], 1)]
theorem eval_atom0332 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0332 = ((g 0) * (g 12) * (g 20)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0332_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11251970553600 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333 : SparsePolynomial.Poly := [([0,13,13], 1)]
theorem eval_atom0333 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0333 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0333_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22298267001600 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334 : SparsePolynomial.Poly := [([0,13,14], 1)]
theorem eval_atom0334 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0334 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0334_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41193039456000 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335 : SparsePolynomial.Poly := [([0,13,15], 1)]
theorem eval_atom0335 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 0) * (g 13) * (g 15)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39191522403600 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block005 : SparsePolynomial.Poly := [([0,6,13], 24337174377600), ([0,6,14], 25039315123200), ([0,6,15], 29039577235200), ([0,6,16], 21558664512000), ([0,6,17], 18654996729600), ([0,6,18], 13125428870400), ([0,6,19], 13510927180800), ([0,6,20], 10819430496000), ([0,7,7], 13421582466048), ([0,7,8], 23660965873728), ([0,7,9], 22372041369024), ([0,7,10], 23033831975424), ([0,7,11], 23838356994624), ([0,7,12], 25176291029824), ([0,7,13], 26078455353024), ([0,7,14], 26761266690624), ([0,7,15], 30796193398176), ([0,7,16], 23976290418336), ([0,7,17], 22287869204832), ([0,7,18], 16973062270560), ([0,7,19], 16137647557920), ([0,7,20], 14405932338336), ([0,8,8], 14770003348800), ([0,8,9], 26552598367680), ([0,8,10], 25135035962400), ([0,8,11], 25813436594400), ([0,8,12], 26983204780000), ([0,8,13], 27823998232800), ([0,8,14], 28445438700000), ([0,8,15], 32314904294400), ([0,8,16], 25706174665500), ([0,8,17], 24255404812800), ([0,8,18], 18917112734100), ([0,8,19], 17491669568100), ([0,8,20], 15923188782900), ([0,9,9], 16313214960000), ([0,9,10], 29540683226880), ([0,9,11], 27605876760000), ([0,9,12], 28779027592000), ([0,9,13], 29516408712000), ([0,9,14], 30034436846400), ([0,9,15], 33814866355200), ([0,9,16], 27205547783400), ([0,9,17], 26091698572800), ([0,9,18], 20444060460600), ([0,9,19], 18430701269400), ([0,9,20], 16915074334200), ([0,10,10], 17758088208000), ([0,10,11], 32512456529280), ([0,10,12], 30716949294080), ([0,10,13], 31264753665600), ([0,10,14], 31637328004800), ([0,10,15], 35314828416000), ([0,10,16], 28584761448600), ([0,10,17], 27927992332800), ([0,10,18], 21666826729800), ([0,10,19], 18956883997800), ([0,10,20], 17385443397000), ([0,11,11], 19284988262400), ([0,11,12], 35899040401280), ([0,11,13], 33134812300800), ([0,11,14], 33319891382400), ([0,11,15], 36736809580800), ([0,11,16], 29709470649600), ([0,11,17], 29218419820800), ([0,11,18], 22050818092800), ([0,11,19], 18736677388800), ([0,11,20], 16733923315200), ([0,12,12], 21251467059200), ([0,12,13], 39297939296000), ([0,12,14], 35912554563200), ([0,12,15], 37646402460800), ([0,12,16], 30033533017600), ([0,12,17], 26922129315200), ([0,12,18], 18741955075200), ([0,12,19], 15709779478400), ([0,12,20], 11251970553600), ([0,13,13], 22298267001600), ([0,13,14], 41193039456000), ([0,13,15], 39191522403600)]
theorem block005_data : block005 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24337174377600 : Int) atom0256) (SparsePolynomial.scale (25039315123200 : Int) atom0257)) (SparsePolynomial.merge (SparsePolynomial.scale (29039577235200 : Int) atom0258) (SparsePolynomial.merge (SparsePolynomial.scale (21558664512000 : Int) atom0259) (SparsePolynomial.scale (18654996729600 : Int) atom0260)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13125428870400 : Int) atom0261) (SparsePolynomial.scale (13510927180800 : Int) atom0262)) (SparsePolynomial.merge (SparsePolynomial.scale (10819430496000 : Int) atom0263) (SparsePolynomial.merge (SparsePolynomial.scale (13421582466048 : Int) atom0264) (SparsePolynomial.scale (23660965873728 : Int) atom0265))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22372041369024 : Int) atom0266) (SparsePolynomial.scale (23033831975424 : Int) atom0267)) (SparsePolynomial.merge (SparsePolynomial.scale (23838356994624 : Int) atom0268) (SparsePolynomial.merge (SparsePolynomial.scale (25176291029824 : Int) atom0269) (SparsePolynomial.scale (26078455353024 : Int) atom0270)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26761266690624 : Int) atom0271) (SparsePolynomial.scale (30796193398176 : Int) atom0272)) (SparsePolynomial.merge (SparsePolynomial.scale (23976290418336 : Int) atom0273) (SparsePolynomial.merge (SparsePolynomial.scale (22287869204832 : Int) atom0274) (SparsePolynomial.scale (16973062270560 : Int) atom0275)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16137647557920 : Int) atom0276) (SparsePolynomial.scale (14405932338336 : Int) atom0277)) (SparsePolynomial.merge (SparsePolynomial.scale (14770003348800 : Int) atom0278) (SparsePolynomial.merge (SparsePolynomial.scale (26552598367680 : Int) atom0279) (SparsePolynomial.scale (25135035962400 : Int) atom0280)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25813436594400 : Int) atom0281) (SparsePolynomial.scale (26983204780000 : Int) atom0282)) (SparsePolynomial.merge (SparsePolynomial.scale (27823998232800 : Int) atom0283) (SparsePolynomial.merge (SparsePolynomial.scale (28445438700000 : Int) atom0284) (SparsePolynomial.scale (32314904294400 : Int) atom0285))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25706174665500 : Int) atom0286) (SparsePolynomial.scale (24255404812800 : Int) atom0287)) (SparsePolynomial.merge (SparsePolynomial.scale (18917112734100 : Int) atom0288) (SparsePolynomial.merge (SparsePolynomial.scale (17491669568100 : Int) atom0289) (SparsePolynomial.scale (15923188782900 : Int) atom0290)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16313214960000 : Int) atom0291) (SparsePolynomial.scale (29540683226880 : Int) atom0292)) (SparsePolynomial.merge (SparsePolynomial.scale (27605876760000 : Int) atom0293) (SparsePolynomial.merge (SparsePolynomial.scale (28779027592000 : Int) atom0294) (SparsePolynomial.scale (29516408712000 : Int) atom0295))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30034436846400 : Int) atom0296) (SparsePolynomial.scale (33814866355200 : Int) atom0297)) (SparsePolynomial.merge (SparsePolynomial.scale (27205547783400 : Int) atom0298) (SparsePolynomial.merge (SparsePolynomial.scale (26091698572800 : Int) atom0299) (SparsePolynomial.scale (20444060460600 : Int) atom0300)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18430701269400 : Int) atom0301) (SparsePolynomial.scale (16915074334200 : Int) atom0302)) (SparsePolynomial.merge (SparsePolynomial.scale (17758088208000 : Int) atom0303) (SparsePolynomial.merge (SparsePolynomial.scale (32512456529280 : Int) atom0304) (SparsePolynomial.scale (30716949294080 : Int) atom0305))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31264753665600 : Int) atom0306) (SparsePolynomial.scale (31637328004800 : Int) atom0307)) (SparsePolynomial.merge (SparsePolynomial.scale (35314828416000 : Int) atom0308) (SparsePolynomial.merge (SparsePolynomial.scale (28584761448600 : Int) atom0309) (SparsePolynomial.scale (27927992332800 : Int) atom0310)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21666826729800 : Int) atom0311) (SparsePolynomial.scale (18956883997800 : Int) atom0312)) (SparsePolynomial.merge (SparsePolynomial.scale (17385443397000 : Int) atom0313) (SparsePolynomial.merge (SparsePolynomial.scale (19284988262400 : Int) atom0314) (SparsePolynomial.scale (35899040401280 : Int) atom0315)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (33134812300800 : Int) atom0316) (SparsePolynomial.scale (33319891382400 : Int) atom0317)) (SparsePolynomial.merge (SparsePolynomial.scale (36736809580800 : Int) atom0318) (SparsePolynomial.merge (SparsePolynomial.scale (29709470649600 : Int) atom0319) (SparsePolynomial.scale (29218419820800 : Int) atom0320)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22050818092800 : Int) atom0321) (SparsePolynomial.scale (18736677388800 : Int) atom0322)) (SparsePolynomial.merge (SparsePolynomial.scale (16733923315200 : Int) atom0323) (SparsePolynomial.merge (SparsePolynomial.scale (21251467059200 : Int) atom0324) (SparsePolynomial.scale (39297939296000 : Int) atom0325))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35912554563200 : Int) atom0326) (SparsePolynomial.scale (37646402460800 : Int) atom0327)) (SparsePolynomial.merge (SparsePolynomial.scale (30033533017600 : Int) atom0328) (SparsePolynomial.merge (SparsePolynomial.scale (26922129315200 : Int) atom0329) (SparsePolynomial.scale (18741955075200 : Int) atom0330)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15709779478400 : Int) atom0331) (SparsePolynomial.scale (11251970553600 : Int) atom0332)) (SparsePolynomial.merge (SparsePolynomial.scale (22298267001600 : Int) atom0333) (SparsePolynomial.merge (SparsePolynomial.scale (41193039456000 : Int) atom0334) (SparsePolynomial.scale (39191522403600 : Int) atom0335)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block005 := by
  rw [block005_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0256_nonneg g hg hA hB) (atom0257_nonneg g hg hA hB)) (add_nonneg (atom0258_nonneg g hg hA hB) (add_nonneg (atom0259_nonneg g hg hA hB) (atom0260_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0261_nonneg g hg hA hB) (atom0262_nonneg g hg hA hB)) (add_nonneg (atom0263_nonneg g hg hA hB) (add_nonneg (atom0264_nonneg g hg hA hB) (atom0265_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0266_nonneg g hg hA hB) (atom0267_nonneg g hg hA hB)) (add_nonneg (atom0268_nonneg g hg hA hB) (add_nonneg (atom0269_nonneg g hg hA hB) (atom0270_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0271_nonneg g hg hA hB) (atom0272_nonneg g hg hA hB)) (add_nonneg (atom0273_nonneg g hg hA hB) (add_nonneg (atom0274_nonneg g hg hA hB) (atom0275_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0276_nonneg g hg hA hB) (atom0277_nonneg g hg hA hB)) (add_nonneg (atom0278_nonneg g hg hA hB) (add_nonneg (atom0279_nonneg g hg hA hB) (atom0280_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0281_nonneg g hg hA hB) (atom0282_nonneg g hg hA hB)) (add_nonneg (atom0283_nonneg g hg hA hB) (add_nonneg (atom0284_nonneg g hg hA hB) (atom0285_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0286_nonneg g hg hA hB) (atom0287_nonneg g hg hA hB)) (add_nonneg (atom0288_nonneg g hg hA hB) (add_nonneg (atom0289_nonneg g hg hA hB) (atom0290_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0291_nonneg g hg hA hB) (atom0292_nonneg g hg hA hB)) (add_nonneg (atom0293_nonneg g hg hA hB) (add_nonneg (atom0294_nonneg g hg hA hB) (atom0295_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0296_nonneg g hg hA hB) (atom0297_nonneg g hg hA hB)) (add_nonneg (atom0298_nonneg g hg hA hB) (add_nonneg (atom0299_nonneg g hg hA hB) (atom0300_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0301_nonneg g hg hA hB) (atom0302_nonneg g hg hA hB)) (add_nonneg (atom0303_nonneg g hg hA hB) (add_nonneg (atom0304_nonneg g hg hA hB) (atom0305_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0306_nonneg g hg hA hB) (atom0307_nonneg g hg hA hB)) (add_nonneg (atom0308_nonneg g hg hA hB) (add_nonneg (atom0309_nonneg g hg hA hB) (atom0310_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0311_nonneg g hg hA hB) (atom0312_nonneg g hg hA hB)) (add_nonneg (atom0313_nonneg g hg hA hB) (add_nonneg (atom0314_nonneg g hg hA hB) (atom0315_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0316_nonneg g hg hA hB) (atom0317_nonneg g hg hA hB)) (add_nonneg (atom0318_nonneg g hg hA hB) (add_nonneg (atom0319_nonneg g hg hA hB) (atom0320_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0321_nonneg g hg hA hB) (atom0322_nonneg g hg hA hB)) (add_nonneg (atom0323_nonneg g hg hA hB) (add_nonneg (atom0324_nonneg g hg hA hB) (atom0325_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0326_nonneg g hg hA hB) (atom0327_nonneg g hg hA hB)) (add_nonneg (atom0328_nonneg g hg hA hB) (add_nonneg (atom0329_nonneg g hg hA hB) (atom0330_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0331_nonneg g hg hA hB) (atom0332_nonneg g hg hA hB)) (add_nonneg (atom0333_nonneg g hg hA hB) (add_nonneg (atom0334_nonneg g hg hA hB) (atom0335_nonneg g hg hA hB))))))))

end APPT.Finite21
