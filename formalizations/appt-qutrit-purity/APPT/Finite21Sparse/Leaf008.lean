import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0496 : SparsePolynomial.Poly := [([1,9,12], 1)]
theorem eval_atom0496 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0496 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0496_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30403816464000 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497 : SparsePolynomial.Poly := [([1,9,13], 1)]
theorem eval_atom0497 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0497 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0497_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29787423120000 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498 : SparsePolynomial.Poly := [([1,9,14], 1)]
theorem eval_atom0498 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0498 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0498_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30487147689600 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499 : SparsePolynomial.Poly := [([1,9,15], 1)]
theorem eval_atom0499 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0499 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0499_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39992545152000 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500 : SparsePolynomial.Poly := [([1,9,16], 1)]
theorem eval_atom0500 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0500 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0500_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34392272014800 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501 : SparsePolynomial.Poly := [([1,9,17], 1)]
theorem eval_atom0501 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0501 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0501_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41077582963200 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502 : SparsePolynomial.Poly := [([1,9,18], 1)]
theorem eval_atom0502 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0502 = ((g 1) * (g 9) * (g 18)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0502_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39334036518000 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503 : SparsePolynomial.Poly := [([1,9,19], 1)]
theorem eval_atom0503 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0503 = ((g 1) * (g 9) * (g 19)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0503_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35737719620400 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504 : SparsePolynomial.Poly := [([1,9,20], 1)]
theorem eval_atom0504 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0504 = ((g 1) * (g 9) * (g 20)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0504_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36469257174000 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505 : SparsePolynomial.Poly := [([1,10,10], 1)]
theorem eval_atom0505 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0505 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0505_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22070559672000 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506 : SparsePolynomial.Poly := [([1,10,11], 1)]
theorem eval_atom0506 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0506 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0506_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39833095538880 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507 : SparsePolynomial.Poly := [([1,10,12], 1)]
theorem eval_atom0507 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0507 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0507_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33381177081280 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508 : SparsePolynomial.Poly := [([1,10,13], 1)]
theorem eval_atom0508 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0508 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0508_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32429753193600 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509 : SparsePolynomial.Poly := [([1,10,14], 1)]
theorem eval_atom0509 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0509 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0509_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32838570172800 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510 : SparsePolynomial.Poly := [([1,10,15], 1)]
theorem eval_atom0510 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0510 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0510_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42138109440000 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511 : SparsePolynomial.Poly := [([1,10,16], 1)]
theorem eval_atom0511 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0511 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0511_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36296339511600 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512 : SparsePolynomial.Poly := [([1,10,17], 1)]
theorem eval_atom0512 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0512 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0512_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43895810649600 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513 : SparsePolynomial.Poly := [([1,10,18], 1)]
theorem eval_atom0513 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0513 = ((g 1) * (g 10) * (g 18)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0513_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40925209222800 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514 : SparsePolynomial.Poly := [([1,10,19], 1)]
theorem eval_atom0514 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0514 = ((g 1) * (g 10) * (g 19)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0514_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36790085077200 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515 : SparsePolynomial.Poly := [([1,10,20], 1)]
theorem eval_atom0515 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0515 = ((g 1) * (g 10) * (g 20)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0515_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37409995299600 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516 : SparsePolynomial.Poly := [([1,11,11], 1)]
theorem eval_atom0516 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0516 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0516_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23509942041600 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517 : SparsePolynomial.Poly := [([1,11,12], 1)]
theorem eval_atom0517 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0517 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0517_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39142615079680 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518 : SparsePolynomial.Poly := [([1,11,13], 1)]
theorem eval_atom0518 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0518 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0518_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34691663462400 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519 : SparsePolynomial.Poly := [([1,11,14], 1)]
theorem eval_atom0519 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0519 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0519_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34725489926400 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520 : SparsePolynomial.Poly := [([1,11,15], 1)]
theorem eval_atom0520 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0520 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0520_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43659826560000 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521 : SparsePolynomial.Poly := [([1,11,16], 1)]
theorem eval_atom0521 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0521 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0521_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37535436288000 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522 : SparsePolynomial.Poly := [([1,11,17], 1)]
theorem eval_atom0522 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0522 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0522_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46090191168000 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523 : SparsePolynomial.Poly := [([1,11,18], 1)]
theorem eval_atom0523 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0523 = ((g 1) * (g 11) * (g 18)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0523_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41618641075200 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524 : SparsePolynomial.Poly := [([1,11,19], 1)]
theorem eval_atom0524 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0524 = ((g 1) * (g 11) * (g 19)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0524_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37129480819200 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525 : SparsePolynomial.Poly := [([1,11,20], 1)]
theorem eval_atom0525 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0525 = ((g 1) * (g 11) * (g 20)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0525_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37510611264000 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526 : SparsePolynomial.Poly := [([1,12,12], 1)]
theorem eval_atom0526 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0526 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0526_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21593669171200 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527 : SparsePolynomial.Poly := [([1,12,13], 1)]
theorem eval_atom0527 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0527 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0527_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37959288304000 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528 : SparsePolynomial.Poly := [([1,12,14], 1)]
theorem eval_atom0528 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0528 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0528_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34193114233600 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529 : SparsePolynomial.Poly := [([1,12,15], 1)]
theorem eval_atom0529 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0529 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0529_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41082437401600 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530 : SparsePolynomial.Poly := [([1,12,16], 1)]
theorem eval_atom0530 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0530 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0530_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36148462828800 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531 : SparsePolynomial.Poly := [([1,12,17], 1)]
theorem eval_atom0531 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0531 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0531_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44185465408000 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532 : SparsePolynomial.Poly := [([1,12,18], 1)]
theorem eval_atom0532 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0532 = ((g 1) * (g 12) * (g 18)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0532_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40050247014400 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533 : SparsePolynomial.Poly := [([1,12,19], 1)]
theorem eval_atom0533 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0533 = ((g 1) * (g 12) * (g 19)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0533_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36979376806400 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534 : SparsePolynomial.Poly := [([1,12,20], 1)]
theorem eval_atom0534 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0534 = ((g 1) * (g 12) * (g 20)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0534_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37173350995200 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535 : SparsePolynomial.Poly := [([1,13,13], 1)]
theorem eval_atom0535 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0535 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0535_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21868118640000 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536 : SparsePolynomial.Poly := [([1,13,14], 1)]
theorem eval_atom0536 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0536 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0536_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39387741782400 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537 : SparsePolynomial.Poly := [([1,13,15], 1)]
theorem eval_atom0537 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0537 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0537_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42390720640800 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538 : SparsePolynomial.Poly := [([1,13,16], 1)]
theorem eval_atom0538 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0538 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0538_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36777587119200 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539 : SparsePolynomial.Poly := [([1,13,17], 1)]
theorem eval_atom0539 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0539 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0539_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45766897344000 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540 : SparsePolynomial.Poly := [([1,13,18], 1)]
theorem eval_atom0540 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0540 = ((g 1) * (g 13) * (g 18)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0540_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41968010649600 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541 : SparsePolynomial.Poly := [([1,13,19], 1)]
theorem eval_atom0541 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0541 = ((g 1) * (g 13) * (g 19)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0541_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35490237040800 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542 : SparsePolynomial.Poly := [([1,13,20], 1)]
theorem eval_atom0542 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0542 = ((g 1) * (g 13) * (g 20)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0542_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38348256844800 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543 : SparsePolynomial.Poly := [([1,14,14], 1)]
theorem eval_atom0543 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0543 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0543_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23400181324800 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544 : SparsePolynomial.Poly := [([1,14,15], 1)]
theorem eval_atom0544 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0544 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0544_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44739847756800 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545 : SparsePolynomial.Poly := [([1,14,16], 1)]
theorem eval_atom0545 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0545 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0545_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38224548633600 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546 : SparsePolynomial.Poly := [([1,14,17], 1)]
theorem eval_atom0546 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0546 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0546_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49103153164800 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547 : SparsePolynomial.Poly := [([1,14,18], 1)]
theorem eval_atom0547 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0547 = ((g 1) * (g 14) * (g 18)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0547_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45640598169600 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548 : SparsePolynomial.Poly := [([1,14,19], 1)]
theorem eval_atom0548 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0548 = ((g 1) * (g 14) * (g 19)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0548_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35787754598400 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549 : SparsePolynomial.Poly := [([1,14,20], 1)]
theorem eval_atom0549 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0549 = ((g 1) * (g 14) * (g 20)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0549_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41321119795200 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550 : SparsePolynomial.Poly := [([1,15,15], 1)]
theorem eval_atom0550 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0550 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0550_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28066300416000 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551 : SparsePolynomial.Poly := [([1,15,16], 1)]
theorem eval_atom0551 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0551 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0551_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46229500800000 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552 : SparsePolynomial.Poly := [([1,15,17], 1)]
theorem eval_atom0552 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0552 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0552_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61253619033600 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553 : SparsePolynomial.Poly := [([1,15,18], 1)]
theorem eval_atom0553 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0553 = ((g 1) * (g 15) * (g 18)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0553_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57872247552000 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554 : SparsePolynomial.Poly := [([1,15,19], 1)]
theorem eval_atom0554 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0554 = ((g 1) * (g 15) * (g 19)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0554_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36902417126400 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555 : SparsePolynomial.Poly := [([1,15,20], 1)]
theorem eval_atom0555 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0555 = ((g 1) * (g 15) * (g 20)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0555_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42460507857600 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556 : SparsePolynomial.Poly := [([1,16,16], 1)]
theorem eval_atom0556 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0556 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0556_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17241316485120 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557 : SparsePolynomial.Poly := [([1,16,17], 1)]
theorem eval_atom0557 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0557 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0557_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44781522508800 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558 : SparsePolynomial.Poly := [([1,16,18], 1)]
theorem eval_atom0558 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0558 = ((g 1) * (g 16) * (g 18)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0558_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48663717580800 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559 : SparsePolynomial.Poly := [([1,16,19], 1)]
theorem eval_atom0559 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0559 = ((g 1) * (g 16) * (g 19)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0559_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34016536512000 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560 : SparsePolynomial.Poly := [([1,16,20], 1)]
theorem eval_atom0560 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0560 = ((g 1) * (g 16) * (g 20)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0560_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35468416670400 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561 : SparsePolynomial.Poly := [([1,17,17], 1)]
theorem eval_atom0561 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0561 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0561_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32332095129600 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562 : SparsePolynomial.Poly := [([1,17,18], 1)]
theorem eval_atom0562 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0562 = ((g 1) * (g 17) * (g 18)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0562_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52531326489600 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563 : SparsePolynomial.Poly := [([1,17,19], 1)]
theorem eval_atom0563 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0563 = ((g 1) * (g 17) * (g 19)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0563_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38858347584000 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564 : SparsePolynomial.Poly := [([1,17,20], 1)]
theorem eval_atom0564 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0564 = ((g 1) * (g 17) * (g 20)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0564_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43189020907200 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565 : SparsePolynomial.Poly := [([1,18,18], 1)]
theorem eval_atom0565 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0565 = ((g 1) * (g 18) * (g 18)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0565_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19281084480000 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566 : SparsePolynomial.Poly := [([1,18,19], 1)]
theorem eval_atom0566 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0566 = ((g 1) * (g 18) * (g 19)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0566_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24781267526400 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567 : SparsePolynomial.Poly := [([1,18,20], 1)]
theorem eval_atom0567 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0567 = ((g 1) * (g 18) * (g 20)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0567_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28558072771200 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568 : SparsePolynomial.Poly := [([1,19,19], 1)]
theorem eval_atom0568 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0568 = ((g 1) * (g 19) * (g 19)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0568_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4012462944000 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569 : SparsePolynomial.Poly := [([1,19,20], 1)]
theorem eval_atom0569 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0569 = ((g 1) * (g 19) * (g 20)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0569_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9601239110400 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570 : SparsePolynomial.Poly := [([1,20,20], 1)]
theorem eval_atom0570 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0570 = ((g 1) * (g 20) * (g 20)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0570_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3467695795200 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0571 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0571 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0571_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4679649676800 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0572 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0572 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0572_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13261906828800 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0573 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0573 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0573_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12484864627200 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0574 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0574 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0574_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13199200388352 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0575 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0575 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0575_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12875483174400 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block008 : SparsePolynomial.Poly := [([1,9,12], 30403816464000), ([1,9,13], 29787423120000), ([1,9,14], 30487147689600), ([1,9,15], 39992545152000), ([1,9,16], 34392272014800), ([1,9,17], 41077582963200), ([1,9,18], 39334036518000), ([1,9,19], 35737719620400), ([1,9,20], 36469257174000), ([1,10,10], 22070559672000), ([1,10,11], 39833095538880), ([1,10,12], 33381177081280), ([1,10,13], 32429753193600), ([1,10,14], 32838570172800), ([1,10,15], 42138109440000), ([1,10,16], 36296339511600), ([1,10,17], 43895810649600), ([1,10,18], 40925209222800), ([1,10,19], 36790085077200), ([1,10,20], 37409995299600), ([1,11,11], 23509942041600), ([1,11,12], 39142615079680), ([1,11,13], 34691663462400), ([1,11,14], 34725489926400), ([1,11,15], 43659826560000), ([1,11,16], 37535436288000), ([1,11,17], 46090191168000), ([1,11,18], 41618641075200), ([1,11,19], 37129480819200), ([1,11,20], 37510611264000), ([1,12,12], 21593669171200), ([1,12,13], 37959288304000), ([1,12,14], 34193114233600), ([1,12,15], 41082437401600), ([1,12,16], 36148462828800), ([1,12,17], 44185465408000), ([1,12,18], 40050247014400), ([1,12,19], 36979376806400), ([1,12,20], 37173350995200), ([1,13,13], 21868118640000), ([1,13,14], 39387741782400), ([1,13,15], 42390720640800), ([1,13,16], 36777587119200), ([1,13,17], 45766897344000), ([1,13,18], 41968010649600), ([1,13,19], 35490237040800), ([1,13,20], 38348256844800), ([1,14,14], 23400181324800), ([1,14,15], 44739847756800), ([1,14,16], 38224548633600), ([1,14,17], 49103153164800), ([1,14,18], 45640598169600), ([1,14,19], 35787754598400), ([1,14,20], 41321119795200), ([1,15,15], 28066300416000), ([1,15,16], 46229500800000), ([1,15,17], 61253619033600), ([1,15,18], 57872247552000), ([1,15,19], 36902417126400), ([1,15,20], 42460507857600), ([1,16,16], 17241316485120), ([1,16,17], 44781522508800), ([1,16,18], 48663717580800), ([1,16,19], 34016536512000), ([1,16,20], 35468416670400), ([1,17,17], 32332095129600), ([1,17,18], 52531326489600), ([1,17,19], 38858347584000), ([1,17,20], 43189020907200), ([1,18,18], 19281084480000), ([1,18,19], 24781267526400), ([1,18,20], 28558072771200), ([1,19,19], 4012462944000), ([1,19,20], 9601239110400), ([1,20,20], 3467695795200), ([2,2,2], 4679649676800), ([2,2,3], 13261906828800), ([2,2,4], 12484864627200), ([2,2,5], 13199200388352), ([2,2,6], 12875483174400)]
theorem block008_data : block008 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30403816464000 : Int) atom0496) (SparsePolynomial.scale (29787423120000 : Int) atom0497)) (SparsePolynomial.merge (SparsePolynomial.scale (30487147689600 : Int) atom0498) (SparsePolynomial.merge (SparsePolynomial.scale (39992545152000 : Int) atom0499) (SparsePolynomial.scale (34392272014800 : Int) atom0500)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (41077582963200 : Int) atom0501) (SparsePolynomial.scale (39334036518000 : Int) atom0502)) (SparsePolynomial.merge (SparsePolynomial.scale (35737719620400 : Int) atom0503) (SparsePolynomial.merge (SparsePolynomial.scale (36469257174000 : Int) atom0504) (SparsePolynomial.scale (22070559672000 : Int) atom0505))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39833095538880 : Int) atom0506) (SparsePolynomial.scale (33381177081280 : Int) atom0507)) (SparsePolynomial.merge (SparsePolynomial.scale (32429753193600 : Int) atom0508) (SparsePolynomial.merge (SparsePolynomial.scale (32838570172800 : Int) atom0509) (SparsePolynomial.scale (42138109440000 : Int) atom0510)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36296339511600 : Int) atom0511) (SparsePolynomial.scale (43895810649600 : Int) atom0512)) (SparsePolynomial.merge (SparsePolynomial.scale (40925209222800 : Int) atom0513) (SparsePolynomial.merge (SparsePolynomial.scale (36790085077200 : Int) atom0514) (SparsePolynomial.scale (37409995299600 : Int) atom0515)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23509942041600 : Int) atom0516) (SparsePolynomial.scale (39142615079680 : Int) atom0517)) (SparsePolynomial.merge (SparsePolynomial.scale (34691663462400 : Int) atom0518) (SparsePolynomial.merge (SparsePolynomial.scale (34725489926400 : Int) atom0519) (SparsePolynomial.scale (43659826560000 : Int) atom0520)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37535436288000 : Int) atom0521) (SparsePolynomial.scale (46090191168000 : Int) atom0522)) (SparsePolynomial.merge (SparsePolynomial.scale (41618641075200 : Int) atom0523) (SparsePolynomial.merge (SparsePolynomial.scale (37129480819200 : Int) atom0524) (SparsePolynomial.scale (37510611264000 : Int) atom0525))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21593669171200 : Int) atom0526) (SparsePolynomial.scale (37959288304000 : Int) atom0527)) (SparsePolynomial.merge (SparsePolynomial.scale (34193114233600 : Int) atom0528) (SparsePolynomial.merge (SparsePolynomial.scale (41082437401600 : Int) atom0529) (SparsePolynomial.scale (36148462828800 : Int) atom0530)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (44185465408000 : Int) atom0531) (SparsePolynomial.scale (40050247014400 : Int) atom0532)) (SparsePolynomial.merge (SparsePolynomial.scale (36979376806400 : Int) atom0533) (SparsePolynomial.merge (SparsePolynomial.scale (37173350995200 : Int) atom0534) (SparsePolynomial.scale (21868118640000 : Int) atom0535))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39387741782400 : Int) atom0536) (SparsePolynomial.scale (42390720640800 : Int) atom0537)) (SparsePolynomial.merge (SparsePolynomial.scale (36777587119200 : Int) atom0538) (SparsePolynomial.merge (SparsePolynomial.scale (45766897344000 : Int) atom0539) (SparsePolynomial.scale (41968010649600 : Int) atom0540)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35490237040800 : Int) atom0541) (SparsePolynomial.scale (38348256844800 : Int) atom0542)) (SparsePolynomial.merge (SparsePolynomial.scale (23400181324800 : Int) atom0543) (SparsePolynomial.merge (SparsePolynomial.scale (44739847756800 : Int) atom0544) (SparsePolynomial.scale (38224548633600 : Int) atom0545))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49103153164800 : Int) atom0546) (SparsePolynomial.scale (45640598169600 : Int) atom0547)) (SparsePolynomial.merge (SparsePolynomial.scale (35787754598400 : Int) atom0548) (SparsePolynomial.merge (SparsePolynomial.scale (41321119795200 : Int) atom0549) (SparsePolynomial.scale (28066300416000 : Int) atom0550)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46229500800000 : Int) atom0551) (SparsePolynomial.scale (61253619033600 : Int) atom0552)) (SparsePolynomial.merge (SparsePolynomial.scale (57872247552000 : Int) atom0553) (SparsePolynomial.merge (SparsePolynomial.scale (36902417126400 : Int) atom0554) (SparsePolynomial.scale (42460507857600 : Int) atom0555)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17241316485120 : Int) atom0556) (SparsePolynomial.scale (44781522508800 : Int) atom0557)) (SparsePolynomial.merge (SparsePolynomial.scale (48663717580800 : Int) atom0558) (SparsePolynomial.merge (SparsePolynomial.scale (34016536512000 : Int) atom0559) (SparsePolynomial.scale (35468416670400 : Int) atom0560)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32332095129600 : Int) atom0561) (SparsePolynomial.scale (52531326489600 : Int) atom0562)) (SparsePolynomial.merge (SparsePolynomial.scale (38858347584000 : Int) atom0563) (SparsePolynomial.merge (SparsePolynomial.scale (43189020907200 : Int) atom0564) (SparsePolynomial.scale (19281084480000 : Int) atom0565))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24781267526400 : Int) atom0566) (SparsePolynomial.scale (28558072771200 : Int) atom0567)) (SparsePolynomial.merge (SparsePolynomial.scale (4012462944000 : Int) atom0568) (SparsePolynomial.merge (SparsePolynomial.scale (9601239110400 : Int) atom0569) (SparsePolynomial.scale (3467695795200 : Int) atom0570)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4679649676800 : Int) atom0571) (SparsePolynomial.scale (13261906828800 : Int) atom0572)) (SparsePolynomial.merge (SparsePolynomial.scale (12484864627200 : Int) atom0573) (SparsePolynomial.merge (SparsePolynomial.scale (13199200388352 : Int) atom0574) (SparsePolynomial.scale (12875483174400 : Int) atom0575)))))))) := by decide +kernel
theorem block008_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block008 := by
  rw [block008_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0496_nonneg g hg hA hB) (atom0497_nonneg g hg hA hB)) (add_nonneg (atom0498_nonneg g hg hA hB) (add_nonneg (atom0499_nonneg g hg hA hB) (atom0500_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0501_nonneg g hg hA hB) (atom0502_nonneg g hg hA hB)) (add_nonneg (atom0503_nonneg g hg hA hB) (add_nonneg (atom0504_nonneg g hg hA hB) (atom0505_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0506_nonneg g hg hA hB) (atom0507_nonneg g hg hA hB)) (add_nonneg (atom0508_nonneg g hg hA hB) (add_nonneg (atom0509_nonneg g hg hA hB) (atom0510_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0511_nonneg g hg hA hB) (atom0512_nonneg g hg hA hB)) (add_nonneg (atom0513_nonneg g hg hA hB) (add_nonneg (atom0514_nonneg g hg hA hB) (atom0515_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0516_nonneg g hg hA hB) (atom0517_nonneg g hg hA hB)) (add_nonneg (atom0518_nonneg g hg hA hB) (add_nonneg (atom0519_nonneg g hg hA hB) (atom0520_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0521_nonneg g hg hA hB) (atom0522_nonneg g hg hA hB)) (add_nonneg (atom0523_nonneg g hg hA hB) (add_nonneg (atom0524_nonneg g hg hA hB) (atom0525_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0526_nonneg g hg hA hB) (atom0527_nonneg g hg hA hB)) (add_nonneg (atom0528_nonneg g hg hA hB) (add_nonneg (atom0529_nonneg g hg hA hB) (atom0530_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0531_nonneg g hg hA hB) (atom0532_nonneg g hg hA hB)) (add_nonneg (atom0533_nonneg g hg hA hB) (add_nonneg (atom0534_nonneg g hg hA hB) (atom0535_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0536_nonneg g hg hA hB) (atom0537_nonneg g hg hA hB)) (add_nonneg (atom0538_nonneg g hg hA hB) (add_nonneg (atom0539_nonneg g hg hA hB) (atom0540_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0541_nonneg g hg hA hB) (atom0542_nonneg g hg hA hB)) (add_nonneg (atom0543_nonneg g hg hA hB) (add_nonneg (atom0544_nonneg g hg hA hB) (atom0545_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0546_nonneg g hg hA hB) (atom0547_nonneg g hg hA hB)) (add_nonneg (atom0548_nonneg g hg hA hB) (add_nonneg (atom0549_nonneg g hg hA hB) (atom0550_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0551_nonneg g hg hA hB) (atom0552_nonneg g hg hA hB)) (add_nonneg (atom0553_nonneg g hg hA hB) (add_nonneg (atom0554_nonneg g hg hA hB) (atom0555_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0556_nonneg g hg hA hB) (atom0557_nonneg g hg hA hB)) (add_nonneg (atom0558_nonneg g hg hA hB) (add_nonneg (atom0559_nonneg g hg hA hB) (atom0560_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0561_nonneg g hg hA hB) (atom0562_nonneg g hg hA hB)) (add_nonneg (atom0563_nonneg g hg hA hB) (add_nonneg (atom0564_nonneg g hg hA hB) (atom0565_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0566_nonneg g hg hA hB) (atom0567_nonneg g hg hA hB)) (add_nonneg (atom0568_nonneg g hg hA hB) (add_nonneg (atom0569_nonneg g hg hA hB) (atom0570_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0571_nonneg g hg hA hB) (atom0572_nonneg g hg hA hB)) (add_nonneg (atom0573_nonneg g hg hA hB) (add_nonneg (atom0574_nonneg g hg hA hB) (atom0575_nonneg g hg hA hB))))))))

end APPT.Finite21
