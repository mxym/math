import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0416 : SparsePolynomial.Poly := [([1,3,19], 1)]
theorem eval_atom0416 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0416 = ((g 1) * (g 3) * (g 19)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0416_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14423604249600 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417 : SparsePolynomial.Poly := [([1,3,20], 1)]
theorem eval_atom0417 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0417 = ((g 1) * (g 3) * (g 20)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0417_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11360537395200 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0418 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0418 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0418_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7526146622400 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0419 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0419 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0419_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14464310141952 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0420 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0420 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0420_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14992217856000 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0421 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0421 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0421_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17536417636608 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0422 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0422 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0422_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18177375283200 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423 : SparsePolynomial.Poly := [([1,4,9], 1)]
theorem eval_atom0423 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0423 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0423_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18668342246400 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424 : SparsePolynomial.Poly := [([1,4,10], 1)]
theorem eval_atom0424 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0424 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0424_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19159309209600 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425 : SparsePolynomial.Poly := [([1,4,11], 1)]
theorem eval_atom0425 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0425 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0425_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19026429004800 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426 : SparsePolynomial.Poly := [([1,4,12], 1)]
theorem eval_atom0426 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0426 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0426_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15199948444800 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427 : SparsePolynomial.Poly := [([1,4,13], 1)]
theorem eval_atom0427 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0427 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0427_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14776849180800 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428 : SparsePolynomial.Poly := [([1,4,14], 1)]
theorem eval_atom0428 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0428 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0428_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15669867830400 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429 : SparsePolynomial.Poly := [([1,4,15], 1)]
theorem eval_atom0429 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0429 = ((g 1) * (g 4) * (g 15)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0429_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24880813977600 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430 : SparsePolynomial.Poly := [([1,4,16], 1)]
theorem eval_atom0430 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0430 = ((g 1) * (g 4) * (g 16)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0430_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18272069247600 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431 : SparsePolynomial.Poly := [([1,4,17], 1)]
theorem eval_atom0431 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0431 = ((g 1) * (g 4) * (g 17)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0431_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22602534796800 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432 : SparsePolynomial.Poly := [([1,4,18], 1)]
theorem eval_atom0432 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0432 = ((g 1) * (g 4) * (g 18)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0432_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20221399774800 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433 : SparsePolynomial.Poly := [([1,4,19], 1)]
theorem eval_atom0433 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0433 = ((g 1) * (g 4) * (g 19)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0433_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21663695768400 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434 : SparsePolynomial.Poly := [([1,4,20], 1)]
theorem eval_atom0434 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0434 = ((g 1) * (g 4) * (g 20)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0434_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17565700194000 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0435 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0435 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0435_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11219811941376 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0436 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0436 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0436_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19865648451456 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0437 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0437 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0437_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19588073217408 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0438 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0438 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0438_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20097013768704 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439 : SparsePolynomial.Poly := [([1,5,9], 1)]
theorem eval_atom0439 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0439 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0439_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21289155007104 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440 : SparsePolynomial.Poly := [([1,5,10], 1)]
theorem eval_atom0440 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0440 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0440_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21751611093504 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441 : SparsePolynomial.Poly := [([1,5,11], 1)]
theorem eval_atom0441 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0441 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0441_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21955062587904 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442 : SparsePolynomial.Poly := [([1,5,12], 1)]
theorem eval_atom0442 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0442 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0442_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18753888376704 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443 : SparsePolynomial.Poly := [([1,5,13], 1)]
theorem eval_atom0443 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0443 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0443_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18329339407104 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444 : SparsePolynomial.Poly := [([1,5,14], 1)]
theorem eval_atom0444 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0444 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0444_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19351865090304 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445 : SparsePolynomial.Poly := [([1,5,15], 1)]
theorem eval_atom0445 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0445 = ((g 1) * (g 5) * (g 15)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0445_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29154774357504 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446 : SparsePolynomial.Poly := [([1,5,16], 1)]
theorem eval_atom0446 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0446 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0446_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22695246099072 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447 : SparsePolynomial.Poly := [([1,5,17], 1)]
theorem eval_atom0447 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0447 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0447_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27549158575104 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448 : SparsePolynomial.Poly := [([1,5,18], 1)]
theorem eval_atom0448 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0448 = ((g 1) * (g 5) * (g 18)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0448_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25867921742208 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449 : SparsePolynomial.Poly := [([1,5,19], 1)]
theorem eval_atom0449 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0449 = ((g 1) * (g 5) * (g 19)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0449_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27674310760320 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450 : SparsePolynomial.Poly := [([1,5,20], 1)]
theorem eval_atom0450 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0450 = ((g 1) * (g 5) * (g 20)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0450_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23463825855168 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0451 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0451 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0451_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14524199424000 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0452 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0452 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0452_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25592052764160 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0453 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0453 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0453_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23065383297600 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454 : SparsePolynomial.Poly := [([1,6,9], 1)]
theorem eval_atom0454 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0454 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0454_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22222382918400 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455 : SparsePolynomial.Poly := [([1,6,10], 1)]
theorem eval_atom0455 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0455 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0455_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22859770147200 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456 : SparsePolynomial.Poly := [([1,6,11], 1)]
theorem eval_atom0456 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0456 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0456_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22899764966400 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457 : SparsePolynomial.Poly := [([1,6,12], 1)]
theorem eval_atom0457 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0457 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0457_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20036978572800 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458 : SparsePolynomial.Poly := [([1,6,13], 1)]
theorem eval_atom0458 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0458 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0458_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19788810451200 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459 : SparsePolynomial.Poly := [([1,6,14], 1)]
theorem eval_atom0459 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0459 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0459_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20856760243200 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460 : SparsePolynomial.Poly := [([1,6,15], 1)]
theorem eval_atom0460 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0460 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0460_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31352628787200 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461 : SparsePolynomial.Poly := [([1,6,16], 1)]
theorem eval_atom0461 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0461 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0461_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25110779097600 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462 : SparsePolynomial.Poly := [([1,6,17], 1)]
theorem eval_atom0462 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0462 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0462_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30419676403200 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463 : SparsePolynomial.Poly := [([1,6,18], 1)]
theorem eval_atom0463 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0463 = ((g 1) * (g 6) * (g 18)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0463_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30013882214400 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464 : SparsePolynomial.Poly := [([1,6,19], 1)]
theorem eval_atom0464 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0464 = ((g 1) * (g 6) * (g 19)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0464_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33459931814400 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465 : SparsePolynomial.Poly := [([1,6,20], 1)]
theorem eval_atom0465 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0465 = ((g 1) * (g 6) * (g 20)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0465_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32426062099200 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0466 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0466 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0466_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16601669556480 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0467 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0467 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0467_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29149185627360 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468 : SparsePolynomial.Poly := [([1,7,9], 1)]
theorem eval_atom0468 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0468 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0468_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27058453117056 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469 : SparsePolynomial.Poly := [([1,7,10], 1)]
theorem eval_atom0469 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0469 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0469_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27527674496256 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470 : SparsePolynomial.Poly := [([1,7,11], 1)]
theorem eval_atom0470 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0470 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0470_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27658517533056 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471 : SparsePolynomial.Poly := [([1,7,12], 1)]
theorem eval_atom0471 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0471 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0471_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24757072323456 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472 : SparsePolynomial.Poly := [([1,7,13], 1)]
theorem eval_atom0472 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0472 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0472_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24470245385856 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473 : SparsePolynomial.Poly := [([1,7,14], 1)]
theorem eval_atom0473 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0473 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0473_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25499536361856 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474 : SparsePolynomial.Poly := [([1,7,15], 1)]
theorem eval_atom0474 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0474 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0474_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35551425892608 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475 : SparsePolynomial.Poly := [([1,7,16], 1)]
theorem eval_atom0475 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0475 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0475_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29604979281024 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476 : SparsePolynomial.Poly := [([1,7,17], 1)]
theorem eval_atom0476 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0476 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0476_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35291136907008 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477 : SparsePolynomial.Poly := [([1,7,18], 1)]
theorem eval_atom0477 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0477 = ((g 1) * (g 7) * (g 18)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0477_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34288248159360 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478 : SparsePolynomial.Poly := [([1,7,19], 1)]
theorem eval_atom0478 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0478 = ((g 1) * (g 7) * (g 19)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0478_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34242389905920 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479 : SparsePolynomial.Poly := [([1,7,20], 1)]
theorem eval_atom0479 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0479 = ((g 1) * (g 7) * (g 20)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0479_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32868397290240 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0480 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0480 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0480_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18294922245600 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481 : SparsePolynomial.Poly := [([1,8,9], 1)]
theorem eval_atom0481 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0481 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0481_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32761969339680 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482 : SparsePolynomial.Poly := [([1,8,10], 1)]
theorem eval_atom0482 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0482 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0482_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31025713320000 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483 : SparsePolynomial.Poly := [([1,8,11], 1)]
theorem eval_atom0483 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0483 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0483_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30904307582400 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484 : SparsePolynomial.Poly := [([1,8,12], 1)]
theorem eval_atom0484 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0484 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0484_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27666530673600 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485 : SparsePolynomial.Poly := [([1,8,13], 1)]
theorem eval_atom0485 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0485 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0485_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27256961995200 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486 : SparsePolynomial.Poly := [([1,8,14], 1)]
theorem eval_atom0486 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0486 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0486_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28163511230400 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487 : SparsePolynomial.Poly := [([1,8,15], 1)]
theorem eval_atom0487 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0487 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0487_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37846980864000 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488 : SparsePolynomial.Poly := [([1,8,16], 1)]
theorem eval_atom0488 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0488 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0488_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32247885612600 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489 : SparsePolynomial.Poly := [([1,8,17], 1)]
theorem eval_atom0489 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0489 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0489_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38259355276800 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490 : SparsePolynomial.Poly := [([1,8,18], 1)]
theorem eval_atom0490 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0490 = ((g 1) * (g 8) * (g 18)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0490_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37134500898600 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491 : SparsePolynomial.Poly := [([1,8,19], 1)]
theorem eval_atom0491 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0491 = ((g 1) * (g 8) * (g 19)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0491_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34636711842600 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492 : SparsePolynomial.Poly := [([1,8,20], 1)]
theorem eval_atom0492 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0492 = ((g 1) * (g 8) * (g 20)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0492_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34485486071400 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493 : SparsePolynomial.Poly := [([1,9,9], 1)]
theorem eval_atom0493 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0493 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0493_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20214453268800 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494 : SparsePolynomial.Poly := [([1,9,10], 1)]
theorem eval_atom0494 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0494 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0494_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36537606766080 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495 : SparsePolynomial.Poly := [([1,9,11], 1)]
theorem eval_atom0495 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0495 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0495_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33634828080000 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block007 : SparsePolynomial.Poly := [([1,3,19], 14423604249600), ([1,3,20], 11360537395200), ([1,4,4], 7526146622400), ([1,4,5], 14464310141952), ([1,4,6], 14992217856000), ([1,4,7], 17536417636608), ([1,4,8], 18177375283200), ([1,4,9], 18668342246400), ([1,4,10], 19159309209600), ([1,4,11], 19026429004800), ([1,4,12], 15199948444800), ([1,4,13], 14776849180800), ([1,4,14], 15669867830400), ([1,4,15], 24880813977600), ([1,4,16], 18272069247600), ([1,4,17], 22602534796800), ([1,4,18], 20221399774800), ([1,4,19], 21663695768400), ([1,4,20], 17565700194000), ([1,5,5], 11219811941376), ([1,5,6], 19865648451456), ([1,5,7], 19588073217408), ([1,5,8], 20097013768704), ([1,5,9], 21289155007104), ([1,5,10], 21751611093504), ([1,5,11], 21955062587904), ([1,5,12], 18753888376704), ([1,5,13], 18329339407104), ([1,5,14], 19351865090304), ([1,5,15], 29154774357504), ([1,5,16], 22695246099072), ([1,5,17], 27549158575104), ([1,5,18], 25867921742208), ([1,5,19], 27674310760320), ([1,5,20], 23463825855168), ([1,6,6], 14524199424000), ([1,6,7], 25592052764160), ([1,6,8], 23065383297600), ([1,6,9], 22222382918400), ([1,6,10], 22859770147200), ([1,6,11], 22899764966400), ([1,6,12], 20036978572800), ([1,6,13], 19788810451200), ([1,6,14], 20856760243200), ([1,6,15], 31352628787200), ([1,6,16], 25110779097600), ([1,6,17], 30419676403200), ([1,6,18], 30013882214400), ([1,6,19], 33459931814400), ([1,6,20], 32426062099200), ([1,7,7], 16601669556480), ([1,7,8], 29149185627360), ([1,7,9], 27058453117056), ([1,7,10], 27527674496256), ([1,7,11], 27658517533056), ([1,7,12], 24757072323456), ([1,7,13], 24470245385856), ([1,7,14], 25499536361856), ([1,7,15], 35551425892608), ([1,7,16], 29604979281024), ([1,7,17], 35291136907008), ([1,7,18], 34288248159360), ([1,7,19], 34242389905920), ([1,7,20], 32868397290240), ([1,8,8], 18294922245600), ([1,8,9], 32761969339680), ([1,8,10], 31025713320000), ([1,8,11], 30904307582400), ([1,8,12], 27666530673600), ([1,8,13], 27256961995200), ([1,8,14], 28163511230400), ([1,8,15], 37846980864000), ([1,8,16], 32247885612600), ([1,8,17], 38259355276800), ([1,8,18], 37134500898600), ([1,8,19], 34636711842600), ([1,8,20], 34485486071400), ([1,9,9], 20214453268800), ([1,9,10], 36537606766080), ([1,9,11], 33634828080000)]
theorem block007_data : block007 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14423604249600 : Int) atom0416) (SparsePolynomial.scale (11360537395200 : Int) atom0417)) (SparsePolynomial.merge (SparsePolynomial.scale (7526146622400 : Int) atom0418) (SparsePolynomial.merge (SparsePolynomial.scale (14464310141952 : Int) atom0419) (SparsePolynomial.scale (14992217856000 : Int) atom0420)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17536417636608 : Int) atom0421) (SparsePolynomial.scale (18177375283200 : Int) atom0422)) (SparsePolynomial.merge (SparsePolynomial.scale (18668342246400 : Int) atom0423) (SparsePolynomial.merge (SparsePolynomial.scale (19159309209600 : Int) atom0424) (SparsePolynomial.scale (19026429004800 : Int) atom0425))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15199948444800 : Int) atom0426) (SparsePolynomial.scale (14776849180800 : Int) atom0427)) (SparsePolynomial.merge (SparsePolynomial.scale (15669867830400 : Int) atom0428) (SparsePolynomial.merge (SparsePolynomial.scale (24880813977600 : Int) atom0429) (SparsePolynomial.scale (18272069247600 : Int) atom0430)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22602534796800 : Int) atom0431) (SparsePolynomial.scale (20221399774800 : Int) atom0432)) (SparsePolynomial.merge (SparsePolynomial.scale (21663695768400 : Int) atom0433) (SparsePolynomial.merge (SparsePolynomial.scale (17565700194000 : Int) atom0434) (SparsePolynomial.scale (11219811941376 : Int) atom0435)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19865648451456 : Int) atom0436) (SparsePolynomial.scale (19588073217408 : Int) atom0437)) (SparsePolynomial.merge (SparsePolynomial.scale (20097013768704 : Int) atom0438) (SparsePolynomial.merge (SparsePolynomial.scale (21289155007104 : Int) atom0439) (SparsePolynomial.scale (21751611093504 : Int) atom0440)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21955062587904 : Int) atom0441) (SparsePolynomial.scale (18753888376704 : Int) atom0442)) (SparsePolynomial.merge (SparsePolynomial.scale (18329339407104 : Int) atom0443) (SparsePolynomial.merge (SparsePolynomial.scale (19351865090304 : Int) atom0444) (SparsePolynomial.scale (29154774357504 : Int) atom0445))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22695246099072 : Int) atom0446) (SparsePolynomial.scale (27549158575104 : Int) atom0447)) (SparsePolynomial.merge (SparsePolynomial.scale (25867921742208 : Int) atom0448) (SparsePolynomial.merge (SparsePolynomial.scale (27674310760320 : Int) atom0449) (SparsePolynomial.scale (23463825855168 : Int) atom0450)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14524199424000 : Int) atom0451) (SparsePolynomial.scale (25592052764160 : Int) atom0452)) (SparsePolynomial.merge (SparsePolynomial.scale (23065383297600 : Int) atom0453) (SparsePolynomial.merge (SparsePolynomial.scale (22222382918400 : Int) atom0454) (SparsePolynomial.scale (22859770147200 : Int) atom0455))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22899764966400 : Int) atom0456) (SparsePolynomial.scale (20036978572800 : Int) atom0457)) (SparsePolynomial.merge (SparsePolynomial.scale (19788810451200 : Int) atom0458) (SparsePolynomial.merge (SparsePolynomial.scale (20856760243200 : Int) atom0459) (SparsePolynomial.scale (31352628787200 : Int) atom0460)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25110779097600 : Int) atom0461) (SparsePolynomial.scale (30419676403200 : Int) atom0462)) (SparsePolynomial.merge (SparsePolynomial.scale (30013882214400 : Int) atom0463) (SparsePolynomial.merge (SparsePolynomial.scale (33459931814400 : Int) atom0464) (SparsePolynomial.scale (32426062099200 : Int) atom0465))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16601669556480 : Int) atom0466) (SparsePolynomial.scale (29149185627360 : Int) atom0467)) (SparsePolynomial.merge (SparsePolynomial.scale (27058453117056 : Int) atom0468) (SparsePolynomial.merge (SparsePolynomial.scale (27527674496256 : Int) atom0469) (SparsePolynomial.scale (27658517533056 : Int) atom0470)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24757072323456 : Int) atom0471) (SparsePolynomial.scale (24470245385856 : Int) atom0472)) (SparsePolynomial.merge (SparsePolynomial.scale (25499536361856 : Int) atom0473) (SparsePolynomial.merge (SparsePolynomial.scale (35551425892608 : Int) atom0474) (SparsePolynomial.scale (29604979281024 : Int) atom0475)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35291136907008 : Int) atom0476) (SparsePolynomial.scale (34288248159360 : Int) atom0477)) (SparsePolynomial.merge (SparsePolynomial.scale (34242389905920 : Int) atom0478) (SparsePolynomial.merge (SparsePolynomial.scale (32868397290240 : Int) atom0479) (SparsePolynomial.scale (18294922245600 : Int) atom0480)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32761969339680 : Int) atom0481) (SparsePolynomial.scale (31025713320000 : Int) atom0482)) (SparsePolynomial.merge (SparsePolynomial.scale (30904307582400 : Int) atom0483) (SparsePolynomial.merge (SparsePolynomial.scale (27666530673600 : Int) atom0484) (SparsePolynomial.scale (27256961995200 : Int) atom0485))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (28163511230400 : Int) atom0486) (SparsePolynomial.scale (37846980864000 : Int) atom0487)) (SparsePolynomial.merge (SparsePolynomial.scale (32247885612600 : Int) atom0488) (SparsePolynomial.merge (SparsePolynomial.scale (38259355276800 : Int) atom0489) (SparsePolynomial.scale (37134500898600 : Int) atom0490)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34636711842600 : Int) atom0491) (SparsePolynomial.scale (34485486071400 : Int) atom0492)) (SparsePolynomial.merge (SparsePolynomial.scale (20214453268800 : Int) atom0493) (SparsePolynomial.merge (SparsePolynomial.scale (36537606766080 : Int) atom0494) (SparsePolynomial.scale (33634828080000 : Int) atom0495)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block007 := by
  rw [block007_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0416_nonneg g hg hA hB) (atom0417_nonneg g hg hA hB)) (add_nonneg (atom0418_nonneg g hg hA hB) (add_nonneg (atom0419_nonneg g hg hA hB) (atom0420_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0421_nonneg g hg hA hB) (atom0422_nonneg g hg hA hB)) (add_nonneg (atom0423_nonneg g hg hA hB) (add_nonneg (atom0424_nonneg g hg hA hB) (atom0425_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0426_nonneg g hg hA hB) (atom0427_nonneg g hg hA hB)) (add_nonneg (atom0428_nonneg g hg hA hB) (add_nonneg (atom0429_nonneg g hg hA hB) (atom0430_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0431_nonneg g hg hA hB) (atom0432_nonneg g hg hA hB)) (add_nonneg (atom0433_nonneg g hg hA hB) (add_nonneg (atom0434_nonneg g hg hA hB) (atom0435_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0436_nonneg g hg hA hB) (atom0437_nonneg g hg hA hB)) (add_nonneg (atom0438_nonneg g hg hA hB) (add_nonneg (atom0439_nonneg g hg hA hB) (atom0440_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0441_nonneg g hg hA hB) (atom0442_nonneg g hg hA hB)) (add_nonneg (atom0443_nonneg g hg hA hB) (add_nonneg (atom0444_nonneg g hg hA hB) (atom0445_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0446_nonneg g hg hA hB) (atom0447_nonneg g hg hA hB)) (add_nonneg (atom0448_nonneg g hg hA hB) (add_nonneg (atom0449_nonneg g hg hA hB) (atom0450_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0451_nonneg g hg hA hB) (atom0452_nonneg g hg hA hB)) (add_nonneg (atom0453_nonneg g hg hA hB) (add_nonneg (atom0454_nonneg g hg hA hB) (atom0455_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0456_nonneg g hg hA hB) (atom0457_nonneg g hg hA hB)) (add_nonneg (atom0458_nonneg g hg hA hB) (add_nonneg (atom0459_nonneg g hg hA hB) (atom0460_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0461_nonneg g hg hA hB) (atom0462_nonneg g hg hA hB)) (add_nonneg (atom0463_nonneg g hg hA hB) (add_nonneg (atom0464_nonneg g hg hA hB) (atom0465_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0466_nonneg g hg hA hB) (atom0467_nonneg g hg hA hB)) (add_nonneg (atom0468_nonneg g hg hA hB) (add_nonneg (atom0469_nonneg g hg hA hB) (atom0470_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0471_nonneg g hg hA hB) (atom0472_nonneg g hg hA hB)) (add_nonneg (atom0473_nonneg g hg hA hB) (add_nonneg (atom0474_nonneg g hg hA hB) (atom0475_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0476_nonneg g hg hA hB) (atom0477_nonneg g hg hA hB)) (add_nonneg (atom0478_nonneg g hg hA hB) (add_nonneg (atom0479_nonneg g hg hA hB) (atom0480_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0481_nonneg g hg hA hB) (atom0482_nonneg g hg hA hB)) (add_nonneg (atom0483_nonneg g hg hA hB) (add_nonneg (atom0484_nonneg g hg hA hB) (atom0485_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0486_nonneg g hg hA hB) (atom0487_nonneg g hg hA hB)) (add_nonneg (atom0488_nonneg g hg hA hB) (add_nonneg (atom0489_nonneg g hg hA hB) (atom0490_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0491_nonneg g hg hA hB) (atom0492_nonneg g hg hA hB)) (add_nonneg (atom0493_nonneg g hg hA hB) (add_nonneg (atom0494_nonneg g hg hA hB) (atom0495_nonneg g hg hA hB))))))))

end APPT.Finite21
