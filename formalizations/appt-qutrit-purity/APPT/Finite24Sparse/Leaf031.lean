import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2289 : SparsePolynomial.Poly := [([12,13,22], 1)]
theorem eval_atom2289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2289 = ((g 12) * (g 13) * (g 22)) := by
  norm_num [atom2289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93303439004160 : Int) atom2289) := by
  rw [SparsePolynomial.eval_scale, eval_atom2289]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2290 : SparsePolynomial.Poly := [([12,13,23], 1)]
theorem eval_atom2290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2290 = ((g 12) * (g 13) * (g 23)) := by
  norm_num [atom2290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144759386217600 : Int) atom2290) := by
  rw [SparsePolynomial.eval_scale, eval_atom2290]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2291 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom2291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2291 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom2291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11813892552000 : Int) atom2291) := by
  rw [SparsePolynomial.eval_scale, eval_atom2291]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2292 : SparsePolynomial.Poly := [([12,14,15], 1)]
theorem eval_atom2292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2292 = ((g 12) * (g 14) * (g 15)) := by
  norm_num [atom2292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20555375702400 : Int) atom2292) := by
  rw [SparsePolynomial.eval_scale, eval_atom2292]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2293 : SparsePolynomial.Poly := [([12,14,16], 1)]
theorem eval_atom2293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2293 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom2293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25700864112000 : Int) atom2293) := by
  rw [SparsePolynomial.eval_scale, eval_atom2293]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2294 : SparsePolynomial.Poly := [([12,14,17], 1)]
theorem eval_atom2294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2294 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom2294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30846352521600 : Int) atom2294) := by
  rw [SparsePolynomial.eval_scale, eval_atom2294]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2295 : SparsePolynomial.Poly := [([12,14,18], 1)]
theorem eval_atom2295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2295 = ((g 12) * (g 14) * (g 18)) := by
  norm_num [atom2295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63030033376992 : Int) atom2295) := by
  rw [SparsePolynomial.eval_scale, eval_atom2295]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2296 : SparsePolynomial.Poly := [([12,14,20], 1)]
theorem eval_atom2296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2296 = ((g 12) * (g 14) * (g 20)) := by
  norm_num [atom2296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (147325511250720 : Int) atom2296) := by
  rw [SparsePolynomial.eval_scale, eval_atom2296]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2297 : SparsePolynomial.Poly := [([12,14,21], 1)]
theorem eval_atom2297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2297 = ((g 12) * (g 14) * (g 21)) := by
  norm_num [atom2297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90760107715200 : Int) atom2297) := by
  rw [SparsePolynomial.eval_scale, eval_atom2297]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2298 : SparsePolynomial.Poly := [([12,14,22], 1)]
theorem eval_atom2298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2298 = ((g 12) * (g 14) * (g 22)) := by
  norm_num [atom2298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158618185165440 : Int) atom2298) := by
  rw [SparsePolynomial.eval_scale, eval_atom2298]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2299 : SparsePolynomial.Poly := [([12,14,23], 1)]
theorem eval_atom2299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2299 = ((g 12) * (g 14) * (g 23)) := by
  norm_num [atom2299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254072443640400 : Int) atom2299) := by
  rw [SparsePolynomial.eval_scale, eval_atom2299]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2300 : SparsePolynomial.Poly := [([12,15,15], 1)]
theorem eval_atom2300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2300 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom2300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28260319348800 : Int) atom2300) := by
  rw [SparsePolynomial.eval_scale, eval_atom2300]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2301 : SparsePolynomial.Poly := [([12,15,16], 1)]
theorem eval_atom2301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2301 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom2301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49355227152000 : Int) atom2301) := by
  rw [SparsePolynomial.eval_scale, eval_atom2301]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2302 : SparsePolynomial.Poly := [([12,15,17], 1)]
theorem eval_atom2302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2302 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom2302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55542570652800 : Int) atom2302) := by
  rw [SparsePolynomial.eval_scale, eval_atom2302]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2303 : SparsePolynomial.Poly := [([12,15,18], 1)]
theorem eval_atom2303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2303 = ((g 12) * (g 15) * (g 18)) := by
  norm_num [atom2303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108801504755136 : Int) atom2303) := by
  rw [SparsePolynomial.eval_scale, eval_atom2303]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2304 : SparsePolynomial.Poly := [([12,15,19], 1)]
theorem eval_atom2304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2304 = ((g 12) * (g 15) * (g 19)) := by
  norm_num [atom2304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58637029386240 : Int) atom2304) := by
  rw [SparsePolynomial.eval_scale, eval_atom2304]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2305 : SparsePolynomial.Poly := [([12,15,20], 1)]
theorem eval_atom2305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2305 = ((g 12) * (g 15) * (g 20)) := by
  norm_num [atom2305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (259360392663360 : Int) atom2305) := by
  rw [SparsePolynomial.eval_scale, eval_atom2305]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2306 : SparsePolynomial.Poly := [([12,15,21], 1)]
theorem eval_atom2306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2306 = ((g 12) * (g 15) * (g 21)) := by
  norm_num [atom2306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (226557274695840 : Int) atom2306) := by
  rw [SparsePolynomial.eval_scale, eval_atom2306]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2307 : SparsePolynomial.Poly := [([12,15,22], 1)]
theorem eval_atom2307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2307 = ((g 12) * (g 15) * (g 22)) := by
  norm_num [atom2307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249624699571584 : Int) atom2307) := by
  rw [SparsePolynomial.eval_scale, eval_atom2307]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2308 : SparsePolynomial.Poly := [([12,15,23], 1)]
theorem eval_atom2308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2308 = ((g 12) * (g 15) * (g 23)) := by
  norm_num [atom2308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (353960904553200 : Int) atom2308) := by
  rw [SparsePolynomial.eval_scale, eval_atom2308]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2309 : SparsePolynomial.Poly := [([12,16,16], 1)]
theorem eval_atom2309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2309 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom2309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43696784577600 : Int) atom2309) := by
  rw [SparsePolynomial.eval_scale, eval_atom2309]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2310 : SparsePolynomial.Poly := [([12,16,17], 1)]
theorem eval_atom2310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2310 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom2310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90519134428800 : Int) atom2310) := by
  rw [SparsePolynomial.eval_scale, eval_atom2310]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2311 : SparsePolynomial.Poly := [([12,16,18], 1)]
theorem eval_atom2311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2311 = ((g 12) * (g 16) * (g 18)) := by
  norm_num [atom2311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140214692166336 : Int) atom2311) := by
  rw [SparsePolynomial.eval_scale, eval_atom2311]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2312 : SparsePolynomial.Poly := [([12,16,19], 1)]
theorem eval_atom2312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2312 = ((g 12) * (g 16) * (g 19)) := by
  norm_num [atom2312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (118395827159040 : Int) atom2312) := by
  rw [SparsePolynomial.eval_scale, eval_atom2312]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2313 : SparsePolynomial.Poly := [([12,16,20], 1)]
theorem eval_atom2313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2313 = ((g 12) * (g 16) * (g 20)) := by
  norm_num [atom2313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (347464800797760 : Int) atom2313) := by
  rw [SparsePolynomial.eval_scale, eval_atom2313]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2314 : SparsePolynomial.Poly := [([12,16,21], 1)]
theorem eval_atom2314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2314 = ((g 12) * (g 16) * (g 21)) := by
  norm_num [atom2314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (335468340836640 : Int) atom2314) := by
  rw [SparsePolynomial.eval_scale, eval_atom2314]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2315 : SparsePolynomial.Poly := [([12,16,22], 1)]
theorem eval_atom2315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2315 = ((g 12) * (g 16) * (g 22)) := by
  norm_num [atom2315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (321549426739584 : Int) atom2315) := by
  rw [SparsePolynomial.eval_scale, eval_atom2315]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2316 : SparsePolynomial.Poly := [([12,16,23], 1)]
theorem eval_atom2316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2316 = ((g 12) * (g 16) * (g 23)) := by
  norm_num [atom2316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (519457604526000 : Int) atom2316) := by
  rw [SparsePolynomial.eval_scale, eval_atom2316]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2317 : SparsePolynomial.Poly := [([12,17,17], 1)]
theorem eval_atom2317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2317 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom2317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64633110696000 : Int) atom2317) := by
  rw [SparsePolynomial.eval_scale, eval_atom2317]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2318 : SparsePolynomial.Poly := [([12,17,18], 1)]
theorem eval_atom2318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2318 = ((g 12) * (g 17) * (g 18)) := by
  norm_num [atom2318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (186526987263936 : Int) atom2318) := by
  rw [SparsePolynomial.eval_scale, eval_atom2318]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2319 : SparsePolynomial.Poly := [([12,17,19], 1)]
theorem eval_atom2319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2319 = ((g 12) * (g 17) * (g 19)) := by
  norm_num [atom2319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (198020101847040 : Int) atom2319) := by
  rw [SparsePolynomial.eval_scale, eval_atom2319]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2320 : SparsePolynomial.Poly := [([12,17,20], 1)]
theorem eval_atom2320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2320 = ((g 12) * (g 17) * (g 20)) := by
  norm_num [atom2320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (460401055076160 : Int) atom2320) := by
  rw [SparsePolynomial.eval_scale, eval_atom2320]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2321 : SparsePolynomial.Poly := [([12,17,21], 1)]
theorem eval_atom2321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2321 = ((g 12) * (g 17) * (g 21)) := by
  norm_num [atom2321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (471694437735840 : Int) atom2321) := by
  rw [SparsePolynomial.eval_scale, eval_atom2321]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2322 : SparsePolynomial.Poly := [([12,17,22], 1)]
theorem eval_atom2322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2322 = ((g 12) * (g 17) * (g 22)) := by
  norm_num [atom2322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (479941683341184 : Int) atom2322) := by
  rw [SparsePolynomial.eval_scale, eval_atom2322]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2323 : SparsePolynomial.Poly := [([12,17,23], 1)]
theorem eval_atom2323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2323 = ((g 12) * (g 17) * (g 23)) := by
  norm_num [atom2323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (696128635263600 : Int) atom2323) := by
  rw [SparsePolynomial.eval_scale, eval_atom2323]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2324 : SparsePolynomial.Poly := [([12,18,18], 1)]
theorem eval_atom2324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2324 = ((g 12) * (g 18) * (g 18)) := by
  norm_num [atom2324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (151845018393024 : Int) atom2324) := by
  rw [SparsePolynomial.eval_scale, eval_atom2324]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2325 : SparsePolynomial.Poly := [([12,18,19], 1)]
theorem eval_atom2325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2325 = ((g 12) * (g 18) * (g 19)) := by
  norm_num [atom2325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (329206824644544 : Int) atom2325) := by
  rw [SparsePolynomial.eval_scale, eval_atom2325]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2326 : SparsePolynomial.Poly := [([12,18,20], 1)]
theorem eval_atom2326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2326 = ((g 12) * (g 18) * (g 20)) := by
  norm_num [atom2326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (621009330277248 : Int) atom2326) := by
  rw [SparsePolynomial.eval_scale, eval_atom2326]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2327 : SparsePolynomial.Poly := [([12,18,21], 1)]
theorem eval_atom2327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2327 = ((g 12) * (g 18) * (g 21)) := by
  norm_num [atom2327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (644312525376960 : Int) atom2327) := by
  rw [SparsePolynomial.eval_scale, eval_atom2327]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2328 : SparsePolynomial.Poly := [([12,18,22], 1)]
theorem eval_atom2328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2328 = ((g 12) * (g 18) * (g 22)) := by
  norm_num [atom2328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (505633160724480 : Int) atom2328) := by
  rw [SparsePolynomial.eval_scale, eval_atom2328]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2329 : SparsePolynomial.Poly := [([12,18,23], 1)]
theorem eval_atom2329 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2329 = ((g 12) * (g 18) * (g 23)) := by
  norm_num [atom2329, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2329_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (763431802113024 : Int) atom2329) := by
  rw [SparsePolynomial.eval_scale, eval_atom2329]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2330 : SparsePolynomial.Poly := [([12,19,19], 1)]
theorem eval_atom2330 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2330 = ((g 12) * (g 19) * (g 19)) := by
  norm_num [atom2330, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2330_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (139381029526464 : Int) atom2330) := by
  rw [SparsePolynomial.eval_scale, eval_atom2330]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2331 : SparsePolynomial.Poly := [([12,19,20], 1)]
theorem eval_atom2331 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2331 = ((g 12) * (g 19) * (g 20)) := by
  norm_num [atom2331, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2331_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (564236889682752 : Int) atom2331) := by
  rw [SparsePolynomial.eval_scale, eval_atom2331]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2332 : SparsePolynomial.Poly := [([12,19,21], 1)]
theorem eval_atom2332 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2332 = ((g 12) * (g 19) * (g 21)) := by
  norm_num [atom2332, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2332_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (661893873071904 : Int) atom2332) := by
  rw [SparsePolynomial.eval_scale, eval_atom2332]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2333 : SparsePolynomial.Poly := [([12,19,22], 1)]
theorem eval_atom2333 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2333 = ((g 12) * (g 19) * (g 22)) := by
  norm_num [atom2333, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2333_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (499016944603008 : Int) atom2333) := by
  rw [SparsePolynomial.eval_scale, eval_atom2333]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2334 : SparsePolynomial.Poly := [([12,19,23], 1)]
theorem eval_atom2334 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2334 = ((g 12) * (g 19) * (g 23)) := by
  norm_num [atom2334, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2334_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (653547015318384 : Int) atom2334) := by
  rw [SparsePolynomial.eval_scale, eval_atom2334]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2335 : SparsePolynomial.Poly := [([12,20,20], 1)]
theorem eval_atom2335 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2335 = ((g 12) * (g 20) * (g 20)) := by
  norm_num [atom2335, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2335_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (402272962559424 : Int) atom2335) := by
  rw [SparsePolynomial.eval_scale, eval_atom2335]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2336 : SparsePolynomial.Poly := [([12,20,21], 1)]
theorem eval_atom2336 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2336 = ((g 12) * (g 20) * (g 21)) := by
  norm_num [atom2336, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2336_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (772992938684736 : Int) atom2336) := by
  rw [SparsePolynomial.eval_scale, eval_atom2336]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2337 : SparsePolynomial.Poly := [([12,20,22], 1)]
theorem eval_atom2337 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2337 = ((g 12) * (g 20) * (g 22)) := by
  norm_num [atom2337, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2337_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (523075355781120 : Int) atom2337) := by
  rw [SparsePolynomial.eval_scale, eval_atom2337]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2338 : SparsePolynomial.Poly := [([12,20,23], 1)]
theorem eval_atom2338 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2338 = ((g 12) * (g 20) * (g 23)) := by
  norm_num [atom2338, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2338_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (448819934618880 : Int) atom2338) := by
  rw [SparsePolynomial.eval_scale, eval_atom2338]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2339 : SparsePolynomial.Poly := [([12,21,21], 1)]
theorem eval_atom2339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2339 = ((g 12) * (g 21) * (g 21)) := by
  norm_num [atom2339, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (327897775234656 : Int) atom2339) := by
  rw [SparsePolynomial.eval_scale, eval_atom2339]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2340 : SparsePolynomial.Poly := [([12,21,22], 1)]
theorem eval_atom2340 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2340 = ((g 12) * (g 21) * (g 22)) := by
  norm_num [atom2340, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2340_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (434805549584256 : Int) atom2340) := by
  rw [SparsePolynomial.eval_scale, eval_atom2340]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2341 : SparsePolynomial.Poly := [([12,21,23], 1)]
theorem eval_atom2341 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2341 = ((g 12) * (g 21) * (g 23)) := by
  norm_num [atom2341, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2341_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (385561625880816 : Int) atom2341) := by
  rw [SparsePolynomial.eval_scale, eval_atom2341]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2342 : SparsePolynomial.Poly := [([12,22,22], 1)]
theorem eval_atom2342 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2342 = ((g 12) * (g 22) * (g 22)) := by
  norm_num [atom2342, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2342_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68278699175040 : Int) atom2342) := by
  rw [SparsePolynomial.eval_scale, eval_atom2342]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2343 : SparsePolynomial.Poly := [([12,22,23], 1)]
theorem eval_atom2343 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2343 = ((g 12) * (g 22) * (g 23)) := by
  norm_num [atom2343, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2343_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100562774904576 : Int) atom2343) := by
  rw [SparsePolynomial.eval_scale, eval_atom2343]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2344 : SparsePolynomial.Poly := [([13,13,13], 1)]
theorem eval_atom2344 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2344 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom2344, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2344_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5136629097600 : Int) atom2344) := by
  rw [SparsePolynomial.eval_scale, eval_atom2344]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2345 : SparsePolynomial.Poly := [([13,13,14], 1)]
theorem eval_atom2345 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2345 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom2345, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2345_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3083040576000 : Int) atom2345) := by
  rw [SparsePolynomial.eval_scale, eval_atom2345]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2346 : SparsePolynomial.Poly := [([13,13,18], 1)]
theorem eval_atom2346 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2346 = ((g 13) * (g 13) * (g 18)) := by
  norm_num [atom2346, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2346_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34624275840000 : Int) atom2346) := by
  rw [SparsePolynomial.eval_scale, eval_atom2346]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2347 : SparsePolynomial.Poly := [([13,13,20], 1)]
theorem eval_atom2347 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2347 = ((g 13) * (g 13) * (g 20)) := by
  norm_num [atom2347, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2347_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49043900505600 : Int) atom2347) := by
  rw [SparsePolynomial.eval_scale, eval_atom2347]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2348 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom2348 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2348 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom2348, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2348_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4108948905600 : Int) atom2348) := by
  rw [SparsePolynomial.eval_scale, eval_atom2348]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2349 : SparsePolynomial.Poly := [([13,14,16], 1)]
theorem eval_atom2349 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2349 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom2349, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2349_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3083040576000 : Int) atom2349) := by
  rw [SparsePolynomial.eval_scale, eval_atom2349]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2350 : SparsePolynomial.Poly := [([13,14,17], 1)]
theorem eval_atom2350 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2350 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom2350, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2350_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6166081152000 : Int) atom2350) := by
  rw [SparsePolynomial.eval_scale, eval_atom2350]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2351 : SparsePolynomial.Poly := [([13,14,18], 1)]
theorem eval_atom2351 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2351 = ((g 13) * (g 14) * (g 18)) := by
  norm_num [atom2351, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2351_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51223348582560 : Int) atom2351) := by
  rw [SparsePolynomial.eval_scale, eval_atom2351]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2352 : SparsePolynomial.Poly := [([13,14,20], 1)]
theorem eval_atom2352 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2352 = ((g 13) * (g 14) * (g 20)) := by
  norm_num [atom2352, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2352_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (132506149960800 : Int) atom2352) := by
  rw [SparsePolynomial.eval_scale, eval_atom2352]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2353 : SparsePolynomial.Poly := [([13,14,21], 1)]
theorem eval_atom2353 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2353 = ((g 13) * (g 14) * (g 21)) := by
  norm_num [atom2353, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2353_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61132353559200 : Int) atom2353) := by
  rw [SparsePolynomial.eval_scale, eval_atom2353]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2354 : SparsePolynomial.Poly := [([13,14,22], 1)]
theorem eval_atom2354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2354 = ((g 13) * (g 14) * (g 22)) := by
  norm_num [atom2354, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93303439004160 : Int) atom2354) := by
  rw [SparsePolynomial.eval_scale, eval_atom2354]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2355 : SparsePolynomial.Poly := [([13,14,23], 1)]
theorem eval_atom2355 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2355 = ((g 13) * (g 14) * (g 23)) := by
  norm_num [atom2355, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2355_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144759386217600 : Int) atom2355) := by
  rw [SparsePolynomial.eval_scale, eval_atom2355]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2356 : SparsePolynomial.Poly := [([13,15,15], 1)]
theorem eval_atom2356 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2356 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom2356, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2356_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12326846716800 : Int) atom2356) := by
  rw [SparsePolynomial.eval_scale, eval_atom2356]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2357 : SparsePolynomial.Poly := [([13,15,16], 1)]
theorem eval_atom2357 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2357 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom2357, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2357_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16446426796800 : Int) atom2357) := by
  rw [SparsePolynomial.eval_scale, eval_atom2357]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2358 : SparsePolynomial.Poly := [([13,15,17], 1)]
theorem eval_atom2358 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2358 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom2358, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2358_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21591915206400 : Int) atom2358) := by
  rw [SparsePolynomial.eval_scale, eval_atom2358]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2359 : SparsePolynomial.Poly := [([13,15,18], 1)]
theorem eval_atom2359 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2359 = ((g 13) * (g 15) * (g 18)) := by
  norm_num [atom2359, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2359_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56573559584640 : Int) atom2359) := by
  rw [SparsePolynomial.eval_scale, eval_atom2359]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2360 : SparsePolynomial.Poly := [([13,15,20], 1)]
theorem eval_atom2360 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2360 = ((g 13) * (g 15) * (g 20)) := by
  norm_num [atom2360, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2360_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193558447555200 : Int) atom2360) := by
  rw [SparsePolynomial.eval_scale, eval_atom2360]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2361 : SparsePolynomial.Poly := [([13,15,21], 1)]
theorem eval_atom2361 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2361 = ((g 13) * (g 15) * (g 21)) := by
  norm_num [atom2361, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2361_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150284455876800 : Int) atom2361) := by
  rw [SparsePolynomial.eval_scale, eval_atom2361]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2362 : SparsePolynomial.Poly := [([13,15,22], 1)]
theorem eval_atom2362 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2362 = ((g 13) * (g 15) * (g 22)) := by
  norm_num [atom2362, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2362_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (167872622480640 : Int) atom2362) := by
  rw [SparsePolynomial.eval_scale, eval_atom2362]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2363 : SparsePolynomial.Poly := [([13,15,23], 1)]
theorem eval_atom2363 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2363 = ((g 13) * (g 15) * (g 23)) := by
  norm_num [atom2363, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2363_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269694894016800 : Int) atom2363) := by
  rw [SparsePolynomial.eval_scale, eval_atom2363]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2364 : SparsePolynomial.Poly := [([13,16,16], 1)]
theorem eval_atom2364 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2364 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom2364, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2364_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23638416278400 : Int) atom2364) := by
  rw [SparsePolynomial.eval_scale, eval_atom2364]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2365 : SparsePolynomial.Poly := [([13,16,17], 1)]
theorem eval_atom2365 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2365 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom2365, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2365_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50381135481600 : Int) atom2365) := by
  rw [SparsePolynomial.eval_scale, eval_atom2365]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2366 : SparsePolynomial.Poly := [([13,16,18], 1)]
theorem eval_atom2366 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2366 = ((g 13) * (g 16) * (g 18)) := by
  norm_num [atom2366, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2366_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83843818128000 : Int) atom2366) := by
  rw [SparsePolynomial.eval_scale, eval_atom2366]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2367 : SparsePolynomial.Poly := [([13,16,19], 1)]
theorem eval_atom2367 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2367 = ((g 13) * (g 16) * (g 19)) := by
  norm_num [atom2367, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2367_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59016453753600 : Int) atom2367) := by
  rw [SparsePolynomial.eval_scale, eval_atom2367]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2368 : SparsePolynomial.Poly := [([13,16,20], 1)]
theorem eval_atom2368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2368 = ((g 13) * (g 16) * (g 20)) := by
  norm_num [atom2368, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (287033436950400 : Int) atom2368) := by
  rw [SparsePolynomial.eval_scale, eval_atom2368]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block031 : SparsePolynomial.Poly := [([12,13,22], 93303439004160), ([12,13,23], 144759386217600), ([12,14,14], 11813892552000), ([12,14,15], 20555375702400), ([12,14,16], 25700864112000), ([12,14,17], 30846352521600), ([12,14,18], 63030033376992), ([12,14,20], 147325511250720), ([12,14,21], 90760107715200), ([12,14,22], 158618185165440), ([12,14,23], 254072443640400), ([12,15,15], 28260319348800), ([12,15,16], 49355227152000), ([12,15,17], 55542570652800), ([12,15,18], 108801504755136), ([12,15,19], 58637029386240), ([12,15,20], 259360392663360), ([12,15,21], 226557274695840), ([12,15,22], 249624699571584), ([12,15,23], 353960904553200), ([12,16,16], 43696784577600), ([12,16,17], 90519134428800), ([12,16,18], 140214692166336), ([12,16,19], 118395827159040), ([12,16,20], 347464800797760), ([12,16,21], 335468340836640), ([12,16,22], 321549426739584), ([12,16,23], 519457604526000), ([12,17,17], 64633110696000), ([12,17,18], 186526987263936), ([12,17,19], 198020101847040), ([12,17,20], 460401055076160), ([12,17,21], 471694437735840), ([12,17,22], 479941683341184), ([12,17,23], 696128635263600), ([12,18,18], 151845018393024), ([12,18,19], 329206824644544), ([12,18,20], 621009330277248), ([12,18,21], 644312525376960), ([12,18,22], 505633160724480), ([12,18,23], 763431802113024), ([12,19,19], 139381029526464), ([12,19,20], 564236889682752), ([12,19,21], 661893873071904), ([12,19,22], 499016944603008), ([12,19,23], 653547015318384), ([12,20,20], 402272962559424), ([12,20,21], 772992938684736), ([12,20,22], 523075355781120), ([12,20,23], 448819934618880), ([12,21,21], 327897775234656), ([12,21,22], 434805549584256), ([12,21,23], 385561625880816), ([12,22,22], 68278699175040), ([12,22,23], 100562774904576), ([13,13,13], 5136629097600), ([13,13,14], 3083040576000), ([13,13,18], 34624275840000), ([13,13,20], 49043900505600), ([13,14,14], 4108948905600), ([13,14,16], 3083040576000), ([13,14,17], 6166081152000), ([13,14,18], 51223348582560), ([13,14,20], 132506149960800), ([13,14,21], 61132353559200), ([13,14,22], 93303439004160), ([13,14,23], 144759386217600), ([13,15,15], 12326846716800), ([13,15,16], 16446426796800), ([13,15,17], 21591915206400), ([13,15,18], 56573559584640), ([13,15,20], 193558447555200), ([13,15,21], 150284455876800), ([13,15,22], 167872622480640), ([13,15,23], 269694894016800), ([13,16,16], 23638416278400), ([13,16,17], 50381135481600), ([13,16,18], 83843818128000), ([13,16,19], 59016453753600), ([13,16,20], 287033436950400)]
theorem block031_data : block031 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (93303439004160 : Int) atom2289) (SparsePolynomial.scale (144759386217600 : Int) atom2290)) (SparsePolynomial.merge (SparsePolynomial.scale (11813892552000 : Int) atom2291) (SparsePolynomial.merge (SparsePolynomial.scale (20555375702400 : Int) atom2292) (SparsePolynomial.scale (25700864112000 : Int) atom2293)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30846352521600 : Int) atom2294) (SparsePolynomial.scale (63030033376992 : Int) atom2295)) (SparsePolynomial.merge (SparsePolynomial.scale (147325511250720 : Int) atom2296) (SparsePolynomial.merge (SparsePolynomial.scale (90760107715200 : Int) atom2297) (SparsePolynomial.scale (158618185165440 : Int) atom2298))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (254072443640400 : Int) atom2299) (SparsePolynomial.scale (28260319348800 : Int) atom2300)) (SparsePolynomial.merge (SparsePolynomial.scale (49355227152000 : Int) atom2301) (SparsePolynomial.merge (SparsePolynomial.scale (55542570652800 : Int) atom2302) (SparsePolynomial.scale (108801504755136 : Int) atom2303)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (58637029386240 : Int) atom2304) (SparsePolynomial.scale (259360392663360 : Int) atom2305)) (SparsePolynomial.merge (SparsePolynomial.scale (226557274695840 : Int) atom2306) (SparsePolynomial.merge (SparsePolynomial.scale (249624699571584 : Int) atom2307) (SparsePolynomial.scale (353960904553200 : Int) atom2308)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (43696784577600 : Int) atom2309) (SparsePolynomial.scale (90519134428800 : Int) atom2310)) (SparsePolynomial.merge (SparsePolynomial.scale (140214692166336 : Int) atom2311) (SparsePolynomial.merge (SparsePolynomial.scale (118395827159040 : Int) atom2312) (SparsePolynomial.scale (347464800797760 : Int) atom2313)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (335468340836640 : Int) atom2314) (SparsePolynomial.scale (321549426739584 : Int) atom2315)) (SparsePolynomial.merge (SparsePolynomial.scale (519457604526000 : Int) atom2316) (SparsePolynomial.merge (SparsePolynomial.scale (64633110696000 : Int) atom2317) (SparsePolynomial.scale (186526987263936 : Int) atom2318))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (198020101847040 : Int) atom2319) (SparsePolynomial.scale (460401055076160 : Int) atom2320)) (SparsePolynomial.merge (SparsePolynomial.scale (471694437735840 : Int) atom2321) (SparsePolynomial.merge (SparsePolynomial.scale (479941683341184 : Int) atom2322) (SparsePolynomial.scale (696128635263600 : Int) atom2323)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (151845018393024 : Int) atom2324) (SparsePolynomial.scale (329206824644544 : Int) atom2325)) (SparsePolynomial.merge (SparsePolynomial.scale (621009330277248 : Int) atom2326) (SparsePolynomial.merge (SparsePolynomial.scale (644312525376960 : Int) atom2327) (SparsePolynomial.scale (505633160724480 : Int) atom2328))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (763431802113024 : Int) atom2329) (SparsePolynomial.scale (139381029526464 : Int) atom2330)) (SparsePolynomial.merge (SparsePolynomial.scale (564236889682752 : Int) atom2331) (SparsePolynomial.merge (SparsePolynomial.scale (661893873071904 : Int) atom2332) (SparsePolynomial.scale (499016944603008 : Int) atom2333)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (653547015318384 : Int) atom2334) (SparsePolynomial.scale (402272962559424 : Int) atom2335)) (SparsePolynomial.merge (SparsePolynomial.scale (772992938684736 : Int) atom2336) (SparsePolynomial.merge (SparsePolynomial.scale (523075355781120 : Int) atom2337) (SparsePolynomial.scale (448819934618880 : Int) atom2338))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (327897775234656 : Int) atom2339) (SparsePolynomial.scale (434805549584256 : Int) atom2340)) (SparsePolynomial.merge (SparsePolynomial.scale (385561625880816 : Int) atom2341) (SparsePolynomial.merge (SparsePolynomial.scale (68278699175040 : Int) atom2342) (SparsePolynomial.scale (100562774904576 : Int) atom2343)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5136629097600 : Int) atom2344) (SparsePolynomial.scale (3083040576000 : Int) atom2345)) (SparsePolynomial.merge (SparsePolynomial.scale (34624275840000 : Int) atom2346) (SparsePolynomial.merge (SparsePolynomial.scale (49043900505600 : Int) atom2347) (SparsePolynomial.scale (4108948905600 : Int) atom2348)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2349) (SparsePolynomial.scale (6166081152000 : Int) atom2350)) (SparsePolynomial.merge (SparsePolynomial.scale (51223348582560 : Int) atom2351) (SparsePolynomial.merge (SparsePolynomial.scale (132506149960800 : Int) atom2352) (SparsePolynomial.scale (61132353559200 : Int) atom2353)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (93303439004160 : Int) atom2354) (SparsePolynomial.scale (144759386217600 : Int) atom2355)) (SparsePolynomial.merge (SparsePolynomial.scale (12326846716800 : Int) atom2356) (SparsePolynomial.merge (SparsePolynomial.scale (16446426796800 : Int) atom2357) (SparsePolynomial.scale (21591915206400 : Int) atom2358))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (56573559584640 : Int) atom2359) (SparsePolynomial.scale (193558447555200 : Int) atom2360)) (SparsePolynomial.merge (SparsePolynomial.scale (150284455876800 : Int) atom2361) (SparsePolynomial.merge (SparsePolynomial.scale (167872622480640 : Int) atom2362) (SparsePolynomial.scale (269694894016800 : Int) atom2363)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23638416278400 : Int) atom2364) (SparsePolynomial.scale (50381135481600 : Int) atom2365)) (SparsePolynomial.merge (SparsePolynomial.scale (83843818128000 : Int) atom2366) (SparsePolynomial.merge (SparsePolynomial.scale (59016453753600 : Int) atom2367) (SparsePolynomial.scale (287033436950400 : Int) atom2368)))))))) := by decide +kernel
theorem block031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block031 := by
  rw [block031_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2289_nonneg g hg hA hB) (atom2290_nonneg g hg hA hB)) (add_nonneg (atom2291_nonneg g hg hA hB) (add_nonneg (atom2292_nonneg g hg hA hB) (atom2293_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2294_nonneg g hg hA hB) (atom2295_nonneg g hg hA hB)) (add_nonneg (atom2296_nonneg g hg hA hB) (add_nonneg (atom2297_nonneg g hg hA hB) (atom2298_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2299_nonneg g hg hA hB) (atom2300_nonneg g hg hA hB)) (add_nonneg (atom2301_nonneg g hg hA hB) (add_nonneg (atom2302_nonneg g hg hA hB) (atom2303_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2304_nonneg g hg hA hB) (atom2305_nonneg g hg hA hB)) (add_nonneg (atom2306_nonneg g hg hA hB) (add_nonneg (atom2307_nonneg g hg hA hB) (atom2308_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2309_nonneg g hg hA hB) (atom2310_nonneg g hg hA hB)) (add_nonneg (atom2311_nonneg g hg hA hB) (add_nonneg (atom2312_nonneg g hg hA hB) (atom2313_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2314_nonneg g hg hA hB) (atom2315_nonneg g hg hA hB)) (add_nonneg (atom2316_nonneg g hg hA hB) (add_nonneg (atom2317_nonneg g hg hA hB) (atom2318_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2319_nonneg g hg hA hB) (atom2320_nonneg g hg hA hB)) (add_nonneg (atom2321_nonneg g hg hA hB) (add_nonneg (atom2322_nonneg g hg hA hB) (atom2323_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2324_nonneg g hg hA hB) (atom2325_nonneg g hg hA hB)) (add_nonneg (atom2326_nonneg g hg hA hB) (add_nonneg (atom2327_nonneg g hg hA hB) (atom2328_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2329_nonneg g hg hA hB) (atom2330_nonneg g hg hA hB)) (add_nonneg (atom2331_nonneg g hg hA hB) (add_nonneg (atom2332_nonneg g hg hA hB) (atom2333_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2334_nonneg g hg hA hB) (atom2335_nonneg g hg hA hB)) (add_nonneg (atom2336_nonneg g hg hA hB) (add_nonneg (atom2337_nonneg g hg hA hB) (atom2338_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2339_nonneg g hg hA hB) (atom2340_nonneg g hg hA hB)) (add_nonneg (atom2341_nonneg g hg hA hB) (add_nonneg (atom2342_nonneg g hg hA hB) (atom2343_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2344_nonneg g hg hA hB) (atom2345_nonneg g hg hA hB)) (add_nonneg (atom2346_nonneg g hg hA hB) (add_nonneg (atom2347_nonneg g hg hA hB) (atom2348_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2349_nonneg g hg hA hB) (atom2350_nonneg g hg hA hB)) (add_nonneg (atom2351_nonneg g hg hA hB) (add_nonneg (atom2352_nonneg g hg hA hB) (atom2353_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2354_nonneg g hg hA hB) (atom2355_nonneg g hg hA hB)) (add_nonneg (atom2356_nonneg g hg hA hB) (add_nonneg (atom2357_nonneg g hg hA hB) (atom2358_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2359_nonneg g hg hA hB) (atom2360_nonneg g hg hA hB)) (add_nonneg (atom2361_nonneg g hg hA hB) (add_nonneg (atom2362_nonneg g hg hA hB) (atom2363_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2364_nonneg g hg hA hB) (atom2365_nonneg g hg hA hB)) (add_nonneg (atom2366_nonneg g hg hA hB) (add_nonneg (atom2367_nonneg g hg hA hB) (atom2368_nonneg g hg hA hB))))))))

end APPT.Finite24
