import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1489 : SparsePolynomial.Poly := [([5,7,17], 1)]
theorem eval_atom1489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1489 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom1489, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32355227510496 : Int) atom1489) := by
  rw [SparsePolynomial.eval_scale, eval_atom1489]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1490 : SparsePolynomial.Poly := [([5,7,18], 1)]
theorem eval_atom1490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1490 = ((g 5) * (g 7) * (g 18)) := by
  norm_num [atom1490, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43745229153648 : Int) atom1490) := by
  rw [SparsePolynomial.eval_scale, eval_atom1490]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1491 : SparsePolynomial.Poly := [([5,7,19], 1)]
theorem eval_atom1491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1491 = ((g 5) * (g 7) * (g 19)) := by
  norm_num [atom1491, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56706432921600 : Int) atom1491) := by
  rw [SparsePolynomial.eval_scale, eval_atom1491]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1492 : SparsePolynomial.Poly := [([5,7,20], 1)]
theorem eval_atom1492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1492 = ((g 5) * (g 7) * (g 20)) := by
  norm_num [atom1492, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76377038711952 : Int) atom1492) := by
  rw [SparsePolynomial.eval_scale, eval_atom1492]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1493 : SparsePolynomial.Poly := [([5,7,21], 1)]
theorem eval_atom1493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1493 = ((g 5) * (g 7) * (g 21)) := by
  norm_num [atom1493, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (133755104320728 : Int) atom1493) := by
  rw [SparsePolynomial.eval_scale, eval_atom1493]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1494 : SparsePolynomial.Poly := [([5,7,22], 1)]
theorem eval_atom1494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1494 = ((g 5) * (g 7) * (g 22)) := by
  norm_num [atom1494, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (191133169929504 : Int) atom1494) := by
  rw [SparsePolynomial.eval_scale, eval_atom1494]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1495 : SparsePolynomial.Poly := [([5,7,23], 1)]
theorem eval_atom1495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1495 = ((g 5) * (g 7) * (g 23)) := by
  norm_num [atom1495, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (252374959277892 : Int) atom1495) := by
  rw [SparsePolynomial.eval_scale, eval_atom1495]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1496 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom1496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1496 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom1496, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30617742364704 : Int) atom1496) := by
  rw [SparsePolynomial.eval_scale, eval_atom1496]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1497 : SparsePolynomial.Poly := [([5,8,9], 1)]
theorem eval_atom1497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1497 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom1497, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48899114252208 : Int) atom1497) := by
  rw [SparsePolynomial.eval_scale, eval_atom1497]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1498 : SparsePolynomial.Poly := [([5,8,10], 1)]
theorem eval_atom1498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1498 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom1498, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21675381235200 : Int) atom1498) := by
  rw [SparsePolynomial.eval_scale, eval_atom1498]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1499 : SparsePolynomial.Poly := [([5,8,11], 1)]
theorem eval_atom1499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1499 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom1499, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31085474131008 : Int) atom1499) := by
  rw [SparsePolynomial.eval_scale, eval_atom1499]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1500 : SparsePolynomial.Poly := [([5,8,12], 1)]
theorem eval_atom1500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1500 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom1500, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58922406959328 : Int) atom1500) := by
  rw [SparsePolynomial.eval_scale, eval_atom1500]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1501 : SparsePolynomial.Poly := [([5,8,13], 1)]
theorem eval_atom1501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1501 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom1501, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53259267609504 : Int) atom1501) := by
  rw [SparsePolynomial.eval_scale, eval_atom1501]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1502 : SparsePolynomial.Poly := [([5,8,14], 1)]
theorem eval_atom1502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1502 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom1502, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43921865443104 : Int) atom1502) := by
  rw [SparsePolynomial.eval_scale, eval_atom1502]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1503 : SparsePolynomial.Poly := [([5,8,15], 1)]
theorem eval_atom1503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1503 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom1503, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50109208943904 : Int) atom1503) := by
  rw [SparsePolynomial.eval_scale, eval_atom1503]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1504 : SparsePolynomial.Poly := [([5,8,16], 1)]
theorem eval_atom1504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1504 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom1504, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56296552444704 : Int) atom1504) := by
  rw [SparsePolynomial.eval_scale, eval_atom1504]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1505 : SparsePolynomial.Poly := [([5,8,17], 1)]
theorem eval_atom1505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1505 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom1505, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62483895945504 : Int) atom1505) := by
  rw [SparsePolynomial.eval_scale, eval_atom1505]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1506 : SparsePolynomial.Poly := [([5,8,18], 1)]
theorem eval_atom1506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1506 = ((g 5) * (g 8) * (g 18)) := by
  norm_num [atom1506, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76832947703952 : Int) atom1506) := by
  rw [SparsePolynomial.eval_scale, eval_atom1506]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1507 : SparsePolynomial.Poly := [([5,8,19], 1)]
theorem eval_atom1507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1507 = ((g 5) * (g 8) * (g 19)) := by
  norm_num [atom1507, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96207152025600 : Int) atom1507) := by
  rw [SparsePolynomial.eval_scale, eval_atom1507]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1508 : SparsePolynomial.Poly := [([5,8,20], 1)]
theorem eval_atom1508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1508 = ((g 5) * (g 8) * (g 20)) := by
  norm_num [atom1508, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (122290758369648 : Int) atom1508) := by
  rw [SparsePolynomial.eval_scale, eval_atom1508]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1509 : SparsePolynomial.Poly := [([5,8,21], 1)]
theorem eval_atom1509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1509 = ((g 5) * (g 8) * (g 21)) := by
  norm_num [atom1509, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193758103116072 : Int) atom1509) := by
  rw [SparsePolynomial.eval_scale, eval_atom1509]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1510 : SparsePolynomial.Poly := [([5,8,22], 1)]
theorem eval_atom1510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1510 = ((g 5) * (g 8) * (g 22)) := by
  norm_num [atom1510, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (265225447862496 : Int) atom1510) := by
  rw [SparsePolynomial.eval_scale, eval_atom1510]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1511 : SparsePolynomial.Poly := [([5,8,23], 1)]
theorem eval_atom1511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1511 = ((g 5) * (g 8) * (g 23)) := by
  norm_num [atom1511, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (340940705202108 : Int) atom1511) := by
  rw [SparsePolynomial.eval_scale, eval_atom1511]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1512 : SparsePolynomial.Poly := [([5,9,9], 1)]
theorem eval_atom1512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1512 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom1512, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50132370389904 : Int) atom1512) := by
  rw [SparsePolynomial.eval_scale, eval_atom1512]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1513 : SparsePolynomial.Poly := [([5,9,10], 1)]
theorem eval_atom1513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1513 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom1513, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73000342255104 : Int) atom1513) := by
  rw [SparsePolynomial.eval_scale, eval_atom1513]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1514 : SparsePolynomial.Poly := [([5,9,11], 1)]
theorem eval_atom1514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1514 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom1514, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60389198950608 : Int) atom1514) := by
  rw [SparsePolynomial.eval_scale, eval_atom1514]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1515 : SparsePolynomial.Poly := [([5,9,12], 1)]
theorem eval_atom1515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1515 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom1515, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91330434703728 : Int) atom1515) := by
  rw [SparsePolynomial.eval_scale, eval_atom1515]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1516 : SparsePolynomial.Poly := [([5,9,13], 1)]
theorem eval_atom1516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1516 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom1516, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82605517126704 : Int) atom1516) := by
  rw [SparsePolynomial.eval_scale, eval_atom1516]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1517 : SparsePolynomial.Poly := [([5,9,14], 1)]
theorem eval_atom1517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1517 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom1517, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73289377309104 : Int) atom1517) := by
  rw [SparsePolynomial.eval_scale, eval_atom1517]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1518 : SparsePolynomial.Poly := [([5,9,15], 1)]
theorem eval_atom1518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1518 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom1518, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79497983158704 : Int) atom1518) := by
  rw [SparsePolynomial.eval_scale, eval_atom1518]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1519 : SparsePolynomial.Poly := [([5,9,16], 1)]
theorem eval_atom1519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1519 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom1519, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (85706589008304 : Int) atom1519) := by
  rw [SparsePolynomial.eval_scale, eval_atom1519]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1520 : SparsePolynomial.Poly := [([5,9,17], 1)]
theorem eval_atom1520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1520 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom1520, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91915194857904 : Int) atom1520) := by
  rw [SparsePolynomial.eval_scale, eval_atom1520]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1521 : SparsePolynomial.Poly := [([5,9,18], 1)]
theorem eval_atom1521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1521 = ((g 5) * (g 9) * (g 18)) := by
  norm_num [atom1521, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110304175786200 : Int) atom1521) := by
  rw [SparsePolynomial.eval_scale, eval_atom1521]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1522 : SparsePolynomial.Poly := [([5,9,19], 1)]
theorem eval_atom1522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1522 = ((g 5) * (g 9) * (g 19)) := by
  norm_num [atom1522, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135921777108480 : Int) atom1522) := by
  rw [SparsePolynomial.eval_scale, eval_atom1522]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1523 : SparsePolynomial.Poly := [([5,9,20], 1)]
theorem eval_atom1523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1523 = ((g 5) * (g 9) * (g 20)) := by
  norm_num [atom1523, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (168248780453160 : Int) atom1523) := by
  rw [SparsePolynomial.eval_scale, eval_atom1523]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1524 : SparsePolynomial.Poly := [([5,9,21], 1)]
theorem eval_atom1524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1524 = ((g 5) * (g 9) * (g 21)) := by
  norm_num [atom1524, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249458858366652 : Int) atom1524) := by
  rw [SparsePolynomial.eval_scale, eval_atom1524]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1525 : SparsePolynomial.Poly := [([5,9,22], 1)]
theorem eval_atom1525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1525 = ((g 5) * (g 9) * (g 22)) := by
  norm_num [atom1525, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (330668936280144 : Int) atom1525) := by
  rw [SparsePolynomial.eval_scale, eval_atom1525]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1526 : SparsePolynomial.Poly := [([5,9,23], 1)]
theorem eval_atom1526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1526 = ((g 5) * (g 9) * (g 23)) := by
  norm_num [atom1526, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (415673127039258 : Int) atom1526) := by
  rw [SparsePolynomial.eval_scale, eval_atom1526]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1527 : SparsePolynomial.Poly := [([5,10,10], 1)]
theorem eval_atom1527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1527 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom1527, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54718970367600 : Int) atom1527) := by
  rw [SparsePolynomial.eval_scale, eval_atom1527]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1528 : SparsePolynomial.Poly := [([5,10,11], 1)]
theorem eval_atom1528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1528 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom1528, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103035403280304 : Int) atom1528) := by
  rw [SparsePolynomial.eval_scale, eval_atom1528]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1529 : SparsePolynomial.Poly := [([5,10,12], 1)]
theorem eval_atom1529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1529 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom1529, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129894268063824 : Int) atom1529) := by
  rw [SparsePolynomial.eval_scale, eval_atom1529]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1530 : SparsePolynomial.Poly := [([5,10,13], 1)]
theorem eval_atom1530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1530 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom1530, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (123253060669200 : Int) atom1530) := by
  rw [SparsePolynomial.eval_scale, eval_atom1530]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1531 : SparsePolynomial.Poly := [([5,10,14], 1)]
theorem eval_atom1531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1531 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom1531, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112937590458000 : Int) atom1531) := by
  rw [SparsePolynomial.eval_scale, eval_atom1531]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1532 : SparsePolynomial.Poly := [([5,10,15], 1)]
theorem eval_atom1532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1532 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom1532, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (118146865914000 : Int) atom1532) := by
  rw [SparsePolynomial.eval_scale, eval_atom1532]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1533 : SparsePolynomial.Poly := [([5,10,16], 1)]
theorem eval_atom1533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1533 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom1533, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (123356141370000 : Int) atom1533) := by
  rw [SparsePolynomial.eval_scale, eval_atom1533]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1534 : SparsePolynomial.Poly := [([5,10,17], 1)]
theorem eval_atom1534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1534 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom1534, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (128565416826000 : Int) atom1534) := by
  rw [SparsePolynomial.eval_scale, eval_atom1534]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1535 : SparsePolynomial.Poly := [([5,10,18], 1)]
theorem eval_atom1535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1535 = ((g 5) * (g 10) * (g 18)) := by
  norm_num [atom1535, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (154777723324488 : Int) atom1535) := by
  rw [SparsePolynomial.eval_scale, eval_atom1535]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1536 : SparsePolynomial.Poly := [([5,10,19], 1)]
theorem eval_atom1536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1536 = ((g 5) * (g 10) * (g 19)) := by
  norm_num [atom1536, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (186951414228480 : Int) atom1536) := by
  rw [SparsePolynomial.eval_scale, eval_atom1536]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1537 : SparsePolynomial.Poly := [([5,10,20], 1)]
theorem eval_atom1537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1537 = ((g 5) * (g 10) * (g 20)) := by
  norm_num [atom1537, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225834507154872 : Int) atom1537) := by
  rw [SparsePolynomial.eval_scale, eval_atom1537]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1538 : SparsePolynomial.Poly := [([5,10,21], 1)]
theorem eval_atom1538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1538 = ((g 5) * (g 10) * (g 21)) := by
  norm_num [atom1538, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (306021256696980 : Int) atom1538) := by
  rw [SparsePolynomial.eval_scale, eval_atom1538]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1539 : SparsePolynomial.Poly := [([5,10,22], 1)]
theorem eval_atom1539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1539 = ((g 5) * (g 10) * (g 22)) := by
  norm_num [atom1539, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (386208006239088 : Int) atom1539) := by
  rw [SparsePolynomial.eval_scale, eval_atom1539]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1540 : SparsePolynomial.Poly := [([5,10,23], 1)]
theorem eval_atom1540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1540 = ((g 5) * (g 10) * (g 23)) := by
  norm_num [atom1540, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (467666395638750 : Int) atom1540) := by
  rw [SparsePolynomial.eval_scale, eval_atom1540]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1541 : SparsePolynomial.Poly := [([5,11,11], 1)]
theorem eval_atom1541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1541 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom1541, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86333512567104 : Int) atom1541) := by
  rw [SparsePolynomial.eval_scale, eval_atom1541]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1542 : SparsePolynomial.Poly := [([5,11,12], 1)]
theorem eval_atom1542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1542 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom1542, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177727995707328 : Int) atom1542) := by
  rw [SparsePolynomial.eval_scale, eval_atom1542]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1543 : SparsePolynomial.Poly := [([5,11,13], 1)]
theorem eval_atom1543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1543 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom1543, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165983824600704 : Int) atom1543) := by
  rw [SparsePolynomial.eval_scale, eval_atom1543]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1544 : SparsePolynomial.Poly := [([5,11,14], 1)]
theorem eval_atom1544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1544 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom1544, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150565390677504 : Int) atom1544) := by
  rw [SparsePolynomial.eval_scale, eval_atom1544]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1545 : SparsePolynomial.Poly := [([5,11,15], 1)]
theorem eval_atom1545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1545 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom1545, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150671702421504 : Int) atom1545) := by
  rw [SparsePolynomial.eval_scale, eval_atom1545]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1546 : SparsePolynomial.Poly := [([5,11,16], 1)]
theorem eval_atom1546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1546 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom1546, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153861054741504 : Int) atom1546) := by
  rw [SparsePolynomial.eval_scale, eval_atom1546]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1547 : SparsePolynomial.Poly := [([5,11,17], 1)]
theorem eval_atom1547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1547 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom1547, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157050407061504 : Int) atom1547) := by
  rw [SparsePolynomial.eval_scale, eval_atom1547]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1548 : SparsePolynomial.Poly := [([5,11,18], 1)]
theorem eval_atom1548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1548 = ((g 5) * (g 11) * (g 18)) := by
  norm_num [atom1548, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (198462683884608 : Int) atom1548) := by
  rw [SparsePolynomial.eval_scale, eval_atom1548]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1549 : SparsePolynomial.Poly := [([5,11,19], 1)]
theorem eval_atom1549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1549 = ((g 5) * (g 11) * (g 19)) := by
  norm_num [atom1549, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (223083434787840 : Int) atom1549) := by
  rw [SparsePolynomial.eval_scale, eval_atom1549]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1550 : SparsePolynomial.Poly := [([5,11,20], 1)]
theorem eval_atom1550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1550 = ((g 5) * (g 11) * (g 20)) := by
  norm_num [atom1550, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (276330381484608 : Int) atom1550) := by
  rw [SparsePolynomial.eval_scale, eval_atom1550]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1551 : SparsePolynomial.Poly := [([5,11,21], 1)]
theorem eval_atom1551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1551 = ((g 5) * (g 11) * (g 21)) := by
  norm_num [atom1551, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (348770785600512 : Int) atom1551) := by
  rw [SparsePolynomial.eval_scale, eval_atom1551]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1552 : SparsePolynomial.Poly := [([5,11,22], 1)]
theorem eval_atom1552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1552 = ((g 5) * (g 11) * (g 22)) := by
  norm_num [atom1552, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (431499235368960 : Int) atom1552) := by
  rw [SparsePolynomial.eval_scale, eval_atom1552]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1553 : SparsePolynomial.Poly := [([5,11,23], 1)]
theorem eval_atom1553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1553 = ((g 5) * (g 11) * (g 23)) := by
  norm_num [atom1553, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (514227685137408 : Int) atom1553) := by
  rw [SparsePolynomial.eval_scale, eval_atom1553]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1554 : SparsePolynomial.Poly := [([5,12,12], 1)]
theorem eval_atom1554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1554 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom1554, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129411562794624 : Int) atom1554) := by
  rw [SparsePolynomial.eval_scale, eval_atom1554]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1555 : SparsePolynomial.Poly := [([5,12,13], 1)]
theorem eval_atom1555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1555 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom1555, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (235307586628224 : Int) atom1555) := by
  rw [SparsePolynomial.eval_scale, eval_atom1555]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1556 : SparsePolynomial.Poly := [([5,12,14], 1)]
theorem eval_atom1556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1556 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom1556, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (219931677402624 : Int) atom1556) := by
  rw [SparsePolynomial.eval_scale, eval_atom1556]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1557 : SparsePolynomial.Poly := [([5,12,15], 1)]
theorem eval_atom1557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1557 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom1557, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220080513844224 : Int) atom1557) := by
  rw [SparsePolynomial.eval_scale, eval_atom1557]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1558 : SparsePolynomial.Poly := [([5,12,16], 1)]
theorem eval_atom1558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1558 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom1558, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220229350285824 : Int) atom1558) := by
  rw [SparsePolynomial.eval_scale, eval_atom1558]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1559 : SparsePolynomial.Poly := [([5,12,17], 1)]
theorem eval_atom1559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1559 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom1559, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220378186727424 : Int) atom1559) := by
  rw [SparsePolynomial.eval_scale, eval_atom1559]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1560 : SparsePolynomial.Poly := [([5,12,18], 1)]
theorem eval_atom1560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1560 = ((g 5) * (g 12) * (g 18)) := by
  norm_num [atom1560, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (284414134232448 : Int) atom1560) := by
  rw [SparsePolynomial.eval_scale, eval_atom1560]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1561 : SparsePolynomial.Poly := [([5,12,19], 1)]
theorem eval_atom1561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1561 = ((g 5) * (g 12) * (g 19)) := by
  norm_num [atom1561, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (271093818378240 : Int) atom1561) := by
  rw [SparsePolynomial.eval_scale, eval_atom1561]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1562 : SparsePolynomial.Poly := [([5,12,20], 1)]
theorem eval_atom1562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1562 = ((g 5) * (g 12) * (g 20)) := by
  norm_num [atom1562, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (374528944741248 : Int) atom1562) := by
  rw [SparsePolynomial.eval_scale, eval_atom1562]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1563 : SparsePolynomial.Poly := [([5,12,21], 1)]
theorem eval_atom1563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1563 = ((g 5) * (g 12) * (g 21)) := by
  norm_num [atom1563, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (372227408796672 : Int) atom1563) := by
  rw [SparsePolynomial.eval_scale, eval_atom1563]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1564 : SparsePolynomial.Poly := [([5,12,22], 1)]
theorem eval_atom1564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1564 = ((g 5) * (g 12) * (g 22)) := by
  norm_num [atom1564, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (439600190261760 : Int) atom1564) := by
  rw [SparsePolynomial.eval_scale, eval_atom1564]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1565 : SparsePolynomial.Poly := [([5,12,23], 1)]
theorem eval_atom1565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1565 = ((g 5) * (g 12) * (g 23)) := by
  norm_num [atom1565, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (506972971726848 : Int) atom1565) := by
  rw [SparsePolynomial.eval_scale, eval_atom1565]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1566 : SparsePolynomial.Poly := [([5,13,13], 1)]
theorem eval_atom1566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1566 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom1566, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (143913103488000 : Int) atom1566) := by
  rw [SparsePolynomial.eval_scale, eval_atom1566]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1567 : SparsePolynomial.Poly := [([5,13,14], 1)]
theorem eval_atom1567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1567 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom1567, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256062342412800 : Int) atom1567) := by
  rw [SparsePolynomial.eval_scale, eval_atom1567]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1568 : SparsePolynomial.Poly := [([5,13,15], 1)]
theorem eval_atom1568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1568 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom1568, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249067029657600 : Int) atom1568) := by
  rw [SparsePolynomial.eval_scale, eval_atom1568]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block021 : SparsePolynomial.Poly := [([5,7,17], 32355227510496), ([5,7,18], 43745229153648), ([5,7,19], 56706432921600), ([5,7,20], 76377038711952), ([5,7,21], 133755104320728), ([5,7,22], 191133169929504), ([5,7,23], 252374959277892), ([5,8,8], 30617742364704), ([5,8,9], 48899114252208), ([5,8,10], 21675381235200), ([5,8,11], 31085474131008), ([5,8,12], 58922406959328), ([5,8,13], 53259267609504), ([5,8,14], 43921865443104), ([5,8,15], 50109208943904), ([5,8,16], 56296552444704), ([5,8,17], 62483895945504), ([5,8,18], 76832947703952), ([5,8,19], 96207152025600), ([5,8,20], 122290758369648), ([5,8,21], 193758103116072), ([5,8,22], 265225447862496), ([5,8,23], 340940705202108), ([5,9,9], 50132370389904), ([5,9,10], 73000342255104), ([5,9,11], 60389198950608), ([5,9,12], 91330434703728), ([5,9,13], 82605517126704), ([5,9,14], 73289377309104), ([5,9,15], 79497983158704), ([5,9,16], 85706589008304), ([5,9,17], 91915194857904), ([5,9,18], 110304175786200), ([5,9,19], 135921777108480), ([5,9,20], 168248780453160), ([5,9,21], 249458858366652), ([5,9,22], 330668936280144), ([5,9,23], 415673127039258), ([5,10,10], 54718970367600), ([5,10,11], 103035403280304), ([5,10,12], 129894268063824), ([5,10,13], 123253060669200), ([5,10,14], 112937590458000), ([5,10,15], 118146865914000), ([5,10,16], 123356141370000), ([5,10,17], 128565416826000), ([5,10,18], 154777723324488), ([5,10,19], 186951414228480), ([5,10,20], 225834507154872), ([5,10,21], 306021256696980), ([5,10,22], 386208006239088), ([5,10,23], 467666395638750), ([5,11,11], 86333512567104), ([5,11,12], 177727995707328), ([5,11,13], 165983824600704), ([5,11,14], 150565390677504), ([5,11,15], 150671702421504), ([5,11,16], 153861054741504), ([5,11,17], 157050407061504), ([5,11,18], 198462683884608), ([5,11,19], 223083434787840), ([5,11,20], 276330381484608), ([5,11,21], 348770785600512), ([5,11,22], 431499235368960), ([5,11,23], 514227685137408), ([5,12,12], 129411562794624), ([5,12,13], 235307586628224), ([5,12,14], 219931677402624), ([5,12,15], 220080513844224), ([5,12,16], 220229350285824), ([5,12,17], 220378186727424), ([5,12,18], 284414134232448), ([5,12,19], 271093818378240), ([5,12,20], 374528944741248), ([5,12,21], 372227408796672), ([5,12,22], 439600190261760), ([5,12,23], 506972971726848), ([5,13,13], 143913103488000), ([5,13,14], 256062342412800), ([5,13,15], 249067029657600)]
theorem block021_data : block021 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32355227510496 : Int) atom1489) (SparsePolynomial.scale (43745229153648 : Int) atom1490)) (SparsePolynomial.merge (SparsePolynomial.scale (56706432921600 : Int) atom1491) (SparsePolynomial.merge (SparsePolynomial.scale (76377038711952 : Int) atom1492) (SparsePolynomial.scale (133755104320728 : Int) atom1493)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (191133169929504 : Int) atom1494) (SparsePolynomial.scale (252374959277892 : Int) atom1495)) (SparsePolynomial.merge (SparsePolynomial.scale (30617742364704 : Int) atom1496) (SparsePolynomial.merge (SparsePolynomial.scale (48899114252208 : Int) atom1497) (SparsePolynomial.scale (21675381235200 : Int) atom1498))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31085474131008 : Int) atom1499) (SparsePolynomial.scale (58922406959328 : Int) atom1500)) (SparsePolynomial.merge (SparsePolynomial.scale (53259267609504 : Int) atom1501) (SparsePolynomial.merge (SparsePolynomial.scale (43921865443104 : Int) atom1502) (SparsePolynomial.scale (50109208943904 : Int) atom1503)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (56296552444704 : Int) atom1504) (SparsePolynomial.scale (62483895945504 : Int) atom1505)) (SparsePolynomial.merge (SparsePolynomial.scale (76832947703952 : Int) atom1506) (SparsePolynomial.merge (SparsePolynomial.scale (96207152025600 : Int) atom1507) (SparsePolynomial.scale (122290758369648 : Int) atom1508)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (193758103116072 : Int) atom1509) (SparsePolynomial.scale (265225447862496 : Int) atom1510)) (SparsePolynomial.merge (SparsePolynomial.scale (340940705202108 : Int) atom1511) (SparsePolynomial.merge (SparsePolynomial.scale (50132370389904 : Int) atom1512) (SparsePolynomial.scale (73000342255104 : Int) atom1513)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (60389198950608 : Int) atom1514) (SparsePolynomial.scale (91330434703728 : Int) atom1515)) (SparsePolynomial.merge (SparsePolynomial.scale (82605517126704 : Int) atom1516) (SparsePolynomial.merge (SparsePolynomial.scale (73289377309104 : Int) atom1517) (SparsePolynomial.scale (79497983158704 : Int) atom1518))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (85706589008304 : Int) atom1519) (SparsePolynomial.scale (91915194857904 : Int) atom1520)) (SparsePolynomial.merge (SparsePolynomial.scale (110304175786200 : Int) atom1521) (SparsePolynomial.merge (SparsePolynomial.scale (135921777108480 : Int) atom1522) (SparsePolynomial.scale (168248780453160 : Int) atom1523)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (249458858366652 : Int) atom1524) (SparsePolynomial.scale (330668936280144 : Int) atom1525)) (SparsePolynomial.merge (SparsePolynomial.scale (415673127039258 : Int) atom1526) (SparsePolynomial.merge (SparsePolynomial.scale (54718970367600 : Int) atom1527) (SparsePolynomial.scale (103035403280304 : Int) atom1528))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (129894268063824 : Int) atom1529) (SparsePolynomial.scale (123253060669200 : Int) atom1530)) (SparsePolynomial.merge (SparsePolynomial.scale (112937590458000 : Int) atom1531) (SparsePolynomial.merge (SparsePolynomial.scale (118146865914000 : Int) atom1532) (SparsePolynomial.scale (123356141370000 : Int) atom1533)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (128565416826000 : Int) atom1534) (SparsePolynomial.scale (154777723324488 : Int) atom1535)) (SparsePolynomial.merge (SparsePolynomial.scale (186951414228480 : Int) atom1536) (SparsePolynomial.merge (SparsePolynomial.scale (225834507154872 : Int) atom1537) (SparsePolynomial.scale (306021256696980 : Int) atom1538))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (386208006239088 : Int) atom1539) (SparsePolynomial.scale (467666395638750 : Int) atom1540)) (SparsePolynomial.merge (SparsePolynomial.scale (86333512567104 : Int) atom1541) (SparsePolynomial.merge (SparsePolynomial.scale (177727995707328 : Int) atom1542) (SparsePolynomial.scale (165983824600704 : Int) atom1543)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (150565390677504 : Int) atom1544) (SparsePolynomial.scale (150671702421504 : Int) atom1545)) (SparsePolynomial.merge (SparsePolynomial.scale (153861054741504 : Int) atom1546) (SparsePolynomial.merge (SparsePolynomial.scale (157050407061504 : Int) atom1547) (SparsePolynomial.scale (198462683884608 : Int) atom1548)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (223083434787840 : Int) atom1549) (SparsePolynomial.scale (276330381484608 : Int) atom1550)) (SparsePolynomial.merge (SparsePolynomial.scale (348770785600512 : Int) atom1551) (SparsePolynomial.merge (SparsePolynomial.scale (431499235368960 : Int) atom1552) (SparsePolynomial.scale (514227685137408 : Int) atom1553)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (129411562794624 : Int) atom1554) (SparsePolynomial.scale (235307586628224 : Int) atom1555)) (SparsePolynomial.merge (SparsePolynomial.scale (219931677402624 : Int) atom1556) (SparsePolynomial.merge (SparsePolynomial.scale (220080513844224 : Int) atom1557) (SparsePolynomial.scale (220229350285824 : Int) atom1558))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (220378186727424 : Int) atom1559) (SparsePolynomial.scale (284414134232448 : Int) atom1560)) (SparsePolynomial.merge (SparsePolynomial.scale (271093818378240 : Int) atom1561) (SparsePolynomial.merge (SparsePolynomial.scale (374528944741248 : Int) atom1562) (SparsePolynomial.scale (372227408796672 : Int) atom1563)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (439600190261760 : Int) atom1564) (SparsePolynomial.scale (506972971726848 : Int) atom1565)) (SparsePolynomial.merge (SparsePolynomial.scale (143913103488000 : Int) atom1566) (SparsePolynomial.merge (SparsePolynomial.scale (256062342412800 : Int) atom1567) (SparsePolynomial.scale (249067029657600 : Int) atom1568)))))))) := by decide +kernel
theorem block021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block021 := by
  rw [block021_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1489_nonneg g hg hA hB) (atom1490_nonneg g hg hA hB)) (add_nonneg (atom1491_nonneg g hg hA hB) (add_nonneg (atom1492_nonneg g hg hA hB) (atom1493_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1494_nonneg g hg hA hB) (atom1495_nonneg g hg hA hB)) (add_nonneg (atom1496_nonneg g hg hA hB) (add_nonneg (atom1497_nonneg g hg hA hB) (atom1498_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1499_nonneg g hg hA hB) (atom1500_nonneg g hg hA hB)) (add_nonneg (atom1501_nonneg g hg hA hB) (add_nonneg (atom1502_nonneg g hg hA hB) (atom1503_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1504_nonneg g hg hA hB) (atom1505_nonneg g hg hA hB)) (add_nonneg (atom1506_nonneg g hg hA hB) (add_nonneg (atom1507_nonneg g hg hA hB) (atom1508_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1509_nonneg g hg hA hB) (atom1510_nonneg g hg hA hB)) (add_nonneg (atom1511_nonneg g hg hA hB) (add_nonneg (atom1512_nonneg g hg hA hB) (atom1513_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1514_nonneg g hg hA hB) (atom1515_nonneg g hg hA hB)) (add_nonneg (atom1516_nonneg g hg hA hB) (add_nonneg (atom1517_nonneg g hg hA hB) (atom1518_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1519_nonneg g hg hA hB) (atom1520_nonneg g hg hA hB)) (add_nonneg (atom1521_nonneg g hg hA hB) (add_nonneg (atom1522_nonneg g hg hA hB) (atom1523_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1524_nonneg g hg hA hB) (atom1525_nonneg g hg hA hB)) (add_nonneg (atom1526_nonneg g hg hA hB) (add_nonneg (atom1527_nonneg g hg hA hB) (atom1528_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1529_nonneg g hg hA hB) (atom1530_nonneg g hg hA hB)) (add_nonneg (atom1531_nonneg g hg hA hB) (add_nonneg (atom1532_nonneg g hg hA hB) (atom1533_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1534_nonneg g hg hA hB) (atom1535_nonneg g hg hA hB)) (add_nonneg (atom1536_nonneg g hg hA hB) (add_nonneg (atom1537_nonneg g hg hA hB) (atom1538_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1539_nonneg g hg hA hB) (atom1540_nonneg g hg hA hB)) (add_nonneg (atom1541_nonneg g hg hA hB) (add_nonneg (atom1542_nonneg g hg hA hB) (atom1543_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1544_nonneg g hg hA hB) (atom1545_nonneg g hg hA hB)) (add_nonneg (atom1546_nonneg g hg hA hB) (add_nonneg (atom1547_nonneg g hg hA hB) (atom1548_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1549_nonneg g hg hA hB) (atom1550_nonneg g hg hA hB)) (add_nonneg (atom1551_nonneg g hg hA hB) (add_nonneg (atom1552_nonneg g hg hA hB) (atom1553_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1554_nonneg g hg hA hB) (atom1555_nonneg g hg hA hB)) (add_nonneg (atom1556_nonneg g hg hA hB) (add_nonneg (atom1557_nonneg g hg hA hB) (atom1558_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1559_nonneg g hg hA hB) (atom1560_nonneg g hg hA hB)) (add_nonneg (atom1561_nonneg g hg hA hB) (add_nonneg (atom1562_nonneg g hg hA hB) (atom1563_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1564_nonneg g hg hA hB) (atom1565_nonneg g hg hA hB)) (add_nonneg (atom1566_nonneg g hg hA hB) (add_nonneg (atom1567_nonneg g hg hA hB) (atom1568_nonneg g hg hA hB))))))))

end APPT.Finite24
