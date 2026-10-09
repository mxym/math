import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1456 : SparsePolynomial.Poly := [([9,9,17], 1)]
theorem eval_atom1456 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1456 = ((g 9) * (g 9) * (g 17)) := by
  norm_num [atom1456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1456_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182739160800 : Int) atom1456) := by
  rw [SparsePolynomial.eval_scale, eval_atom1456]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1457 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom1457 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1457 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom1457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1457_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1457) := by
  rw [SparsePolynomial.eval_scale, eval_atom1457]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1458 : SparsePolynomial.Poly := [([9,10,13], 1)]
theorem eval_atom1458 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1458 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom1458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1458_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1458) := by
  rw [SparsePolynomial.eval_scale, eval_atom1458]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1459 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom1459 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1459 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom1459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1459_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1459) := by
  rw [SparsePolynomial.eval_scale, eval_atom1459]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1460 : SparsePolynomial.Poly := [([9,10,15], 1)]
theorem eval_atom1460 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1460 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom1460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1460_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5669444229120 : Int) atom1460) := by
  rw [SparsePolynomial.eval_scale, eval_atom1460]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1461 : SparsePolynomial.Poly := [([9,10,17], 1)]
theorem eval_atom1461 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1461 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom1461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1461_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6132165580800 : Int) atom1461) := by
  rw [SparsePolynomial.eval_scale, eval_atom1461]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1462 : SparsePolynomial.Poly := [([9,10,18], 1)]
theorem eval_atom1462 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1462 = ((g 9) * (g 10) * (g 18)) := by
  norm_num [atom1462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1462_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1462) := by
  rw [SparsePolynomial.eval_scale, eval_atom1462]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1463 : SparsePolynomial.Poly := [([9,10,19], 1)]
theorem eval_atom1463 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1463 = ((g 9) * (g 10) * (g 19)) := by
  norm_num [atom1463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1463_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1463) := by
  rw [SparsePolynomial.eval_scale, eval_atom1463]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1464 : SparsePolynomial.Poly := [([9,10,20], 1)]
theorem eval_atom1464 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1464 = ((g 9) * (g 10) * (g 20)) := by
  norm_num [atom1464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1464_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1464) := by
  rw [SparsePolynomial.eval_scale, eval_atom1464]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1465 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom1465 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1465 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom1465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1465_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1533788524800 : Int) atom1465) := by
  rw [SparsePolynomial.eval_scale, eval_atom1465]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1466 : SparsePolynomial.Poly := [([9,11,12], 1)]
theorem eval_atom1466 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1466 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom1466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1466_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1876885516800 : Int) atom1466) := by
  rw [SparsePolynomial.eval_scale, eval_atom1466]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1467 : SparsePolynomial.Poly := [([9,11,13], 1)]
theorem eval_atom1467 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1467 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom1467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1467_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2563079500800 : Int) atom1467) := by
  rw [SparsePolynomial.eval_scale, eval_atom1467]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1468 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom1468 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1468 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom1468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1468_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3249273484800 : Int) atom1468) := by
  rw [SparsePolynomial.eval_scale, eval_atom1468]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1469 : SparsePolynomial.Poly := [([9,11,15], 1)]
theorem eval_atom1469 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1469 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom1469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1469_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6681901564800 : Int) atom1469) := by
  rw [SparsePolynomial.eval_scale, eval_atom1469]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1470 : SparsePolynomial.Poly := [([9,11,16], 1)]
theorem eval_atom1470 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1470 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom1470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1470_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1017686224800 : Int) atom1470) := by
  rw [SparsePolynomial.eval_scale, eval_atom1470]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1471 : SparsePolynomial.Poly := [([9,11,17], 1)]
theorem eval_atom1471 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1471 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom1471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1471_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12075930115200 : Int) atom1471) := by
  rw [SparsePolynomial.eval_scale, eval_atom1471]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1472 : SparsePolynomial.Poly := [([9,11,18], 1)]
theorem eval_atom1472 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1472 = ((g 9) * (g 11) * (g 18)) := by
  norm_num [atom1472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1472_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10740378448800 : Int) atom1472) := by
  rw [SparsePolynomial.eval_scale, eval_atom1472]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1473 : SparsePolynomial.Poly := [([9,11,19], 1)]
theorem eval_atom1473 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1473 = ((g 9) * (g 11) * (g 19)) := by
  norm_num [atom1473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1473_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20105092879200 : Int) atom1473) := by
  rw [SparsePolynomial.eval_scale, eval_atom1473]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1474 : SparsePolynomial.Poly := [([9,11,20], 1)]
theorem eval_atom1474 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1474 = ((g 9) * (g 11) * (g 20)) := by
  norm_num [atom1474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1474_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31025632780800 : Int) atom1474) := by
  rw [SparsePolynomial.eval_scale, eval_atom1474]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1475 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom1475 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1475 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom1475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1475_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3074342342400 : Int) atom1475) := by
  rw [SparsePolynomial.eval_scale, eval_atom1475]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1476 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom1476 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1476 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom1476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1476_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6498546969600 : Int) atom1476) := by
  rw [SparsePolynomial.eval_scale, eval_atom1476]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1477 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom1477 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1477 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom1477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1477_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7275589171200 : Int) atom1477) := by
  rw [SparsePolynomial.eval_scale, eval_atom1477]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1478 : SparsePolynomial.Poly := [([9,12,15], 1)]
theorem eval_atom1478 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1478 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom1478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1478_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8588646595200 : Int) atom1478) := by
  rw [SparsePolynomial.eval_scale, eval_atom1478]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1479 : SparsePolynomial.Poly := [([9,12,16], 1)]
theorem eval_atom1479 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1479 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom1479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1479_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6994941380000 : Int) atom1479) := by
  rw [SparsePolynomial.eval_scale, eval_atom1479]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1480 : SparsePolynomial.Poly := [([9,12,17], 1)]
theorem eval_atom1480 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1480 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom1480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1480_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18707359395200 : Int) atom1480) := by
  rw [SparsePolynomial.eval_scale, eval_atom1480]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1481 : SparsePolynomial.Poly := [([9,12,18], 1)]
theorem eval_atom1481 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1481 = ((g 9) * (g 12) * (g 18)) := by
  norm_num [atom1481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1481_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19393808039200 : Int) atom1481) := by
  rw [SparsePolynomial.eval_scale, eval_atom1481]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1482 : SparsePolynomial.Poly := [([9,12,19], 1)]
theorem eval_atom1482 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1482 = ((g 9) * (g 12) * (g 19)) := by
  norm_num [atom1482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1482_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29075845864800 : Int) atom1482) := by
  rw [SparsePolynomial.eval_scale, eval_atom1482]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1483 : SparsePolynomial.Poly := [([9,12,20], 1)]
theorem eval_atom1483 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1483 = ((g 9) * (g 12) * (g 20)) := by
  norm_num [atom1483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1483_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40801239259200 : Int) atom1483) := by
  rw [SparsePolynomial.eval_scale, eval_atom1483]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1484 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom1484 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1484 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom1484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1484_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5863944096000 : Int) atom1484) := by
  rw [SparsePolynomial.eval_scale, eval_atom1484]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1485 : SparsePolynomial.Poly := [([9,13,14], 1)]
theorem eval_atom1485 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1485 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom1485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1485_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11257079040000 : Int) atom1485) := by
  rw [SparsePolynomial.eval_scale, eval_atom1485]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1486 : SparsePolynomial.Poly := [([9,13,15], 1)]
theorem eval_atom1486 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1486 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom1486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1486_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13909039300800 : Int) atom1486) := by
  rw [SparsePolynomial.eval_scale, eval_atom1486]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1487 : SparsePolynomial.Poly := [([9,13,16], 1)]
theorem eval_atom1487 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1487 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom1487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1487_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13518234338400 : Int) atom1487) := by
  rw [SparsePolynomial.eval_scale, eval_atom1487]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1488 : SparsePolynomial.Poly := [([9,13,17], 1)]
theorem eval_atom1488 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1488 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom1488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1488_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29696485795200 : Int) atom1488) := by
  rw [SparsePolynomial.eval_scale, eval_atom1488]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1489 : SparsePolynomial.Poly := [([9,13,18], 1)]
theorem eval_atom1489 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1489 = ((g 9) * (g 13) * (g 18)) := by
  norm_num [atom1489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1489_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32840704461600 : Int) atom1489) := by
  rw [SparsePolynomial.eval_scale, eval_atom1489]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1490 : SparsePolynomial.Poly := [([9,13,19], 1)]
theorem eval_atom1490 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1490 = ((g 9) * (g 13) * (g 19)) := by
  norm_num [atom1490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1490_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37111606192800 : Int) atom1490) := by
  rw [SparsePolynomial.eval_scale, eval_atom1490]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1491 : SparsePolynomial.Poly := [([9,13,20], 1)]
theorem eval_atom1491 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1491 = ((g 9) * (g 13) * (g 20)) := by
  norm_num [atom1491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1491_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55562141678400 : Int) atom1491) := by
  rw [SparsePolynomial.eval_scale, eval_atom1491]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1492 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom1492 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1492 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom1492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1492_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10101226464000 : Int) atom1492) := by
  rw [SparsePolynomial.eval_scale, eval_atom1492]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1493 : SparsePolynomial.Poly := [([9,14,15], 1)]
theorem eval_atom1493 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1493 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom1493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1493_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19117589904000 : Int) atom1493) := by
  rw [SparsePolynomial.eval_scale, eval_atom1493]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1494 : SparsePolynomial.Poly := [([9,14,16], 1)]
theorem eval_atom1494 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1494 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom1494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1494_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19922377860000 : Int) atom1494) := by
  rw [SparsePolynomial.eval_scale, eval_atom1494]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1495 : SparsePolynomial.Poly := [([9,14,17], 1)]
theorem eval_atom1495 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1495 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom1495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1495_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42879142051200 : Int) atom1495) := by
  rw [SparsePolynomial.eval_scale, eval_atom1495]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1496 : SparsePolynomial.Poly := [([9,14,18], 1)]
theorem eval_atom1496 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1496 = ((g 9) * (g 14) * (g 18)) := by
  norm_num [atom1496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1496_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48700483725600 : Int) atom1496) := by
  rw [SparsePolynomial.eval_scale, eval_atom1496]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1497 : SparsePolynomial.Poly := [([9,14,19], 1)]
theorem eval_atom1497 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1497 = ((g 9) * (g 14) * (g 19)) := by
  norm_num [atom1497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1497_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49598093109600 : Int) atom1497) := by
  rw [SparsePolynomial.eval_scale, eval_atom1497]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1498 : SparsePolynomial.Poly := [([9,14,20], 1)]
theorem eval_atom1498 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1498 = ((g 9) * (g 14) * (g 20)) := by
  norm_num [atom1498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1498_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74906046734400 : Int) atom1498) := by
  rw [SparsePolynomial.eval_scale, eval_atom1498]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1499 : SparsePolynomial.Poly := [([9,15,15], 1)]
theorem eval_atom1499 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1499 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom1499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1499_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16795322611200 : Int) atom1499) := by
  rw [SparsePolynomial.eval_scale, eval_atom1499]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1500 : SparsePolynomial.Poly := [([9,15,16], 1)]
theorem eval_atom1500 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1500 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom1500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1500_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35735021557200 : Int) atom1500) := by
  rw [SparsePolynomial.eval_scale, eval_atom1500]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1501 : SparsePolynomial.Poly := [([9,15,17], 1)]
theorem eval_atom1501 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1501 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom1501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1501_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64884545510400 : Int) atom1501) := by
  rw [SparsePolynomial.eval_scale, eval_atom1501]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1502 : SparsePolynomial.Poly := [([9,15,18], 1)]
theorem eval_atom1502 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1502 = ((g 9) * (g 15) * (g 18)) := by
  norm_num [atom1502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1502_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69986611724400 : Int) atom1502) := by
  rw [SparsePolynomial.eval_scale, eval_atom1502]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1503 : SparsePolynomial.Poly := [([9,15,19], 1)]
theorem eval_atom1503 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1503 = ((g 9) * (g 15) * (g 19)) := by
  norm_num [atom1503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1503_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53647060446000 : Int) atom1503) := by
  rw [SparsePolynomial.eval_scale, eval_atom1503]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1504 : SparsePolynomial.Poly := [([9,15,20], 1)]
theorem eval_atom1504 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1504 = ((g 9) * (g 15) * (g 20)) := by
  norm_num [atom1504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1504_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84256708258800 : Int) atom1504) := by
  rw [SparsePolynomial.eval_scale, eval_atom1504]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1505 : SparsePolynomial.Poly := [([9,16,16], 1)]
theorem eval_atom1505 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1505 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom1505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1505_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14605687272960 : Int) atom1505) := by
  rw [SparsePolynomial.eval_scale, eval_atom1505]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1506 : SparsePolynomial.Poly := [([9,16,17], 1)]
theorem eval_atom1506 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1506 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom1506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1506_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55660876311600 : Int) atom1506) := by
  rw [SparsePolynomial.eval_scale, eval_atom1506]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1507 : SparsePolynomial.Poly := [([9,16,18], 1)]
theorem eval_atom1507 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1507 = ((g 9) * (g 16) * (g 18)) := by
  norm_num [atom1507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1507_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65795220880200 : Int) atom1507) := by
  rw [SparsePolynomial.eval_scale, eval_atom1507]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1508 : SparsePolynomial.Poly := [([9,16,19], 1)]
theorem eval_atom1508 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1508 = ((g 9) * (g 16) * (g 19)) := by
  norm_num [atom1508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1508_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48673825250400 : Int) atom1508) := by
  rw [SparsePolynomial.eval_scale, eval_atom1508]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1509 : SparsePolynomial.Poly := [([9,16,20], 1)]
theorem eval_atom1509 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1509 = ((g 9) * (g 16) * (g 20)) := by
  norm_num [atom1509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1509_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66408854078700 : Int) atom1509) := by
  rw [SparsePolynomial.eval_scale, eval_atom1509]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1510 : SparsePolynomial.Poly := [([9,17,17], 1)]
theorem eval_atom1510 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1510 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom1510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1510_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41744447539200 : Int) atom1510) := by
  rw [SparsePolynomial.eval_scale, eval_atom1510]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1511 : SparsePolynomial.Poly := [([9,17,18], 1)]
theorem eval_atom1511 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1511 = ((g 9) * (g 17) * (g 18)) := by
  norm_num [atom1511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1511_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76111510784400 : Int) atom1511) := by
  rw [SparsePolynomial.eval_scale, eval_atom1511]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1512 : SparsePolynomial.Poly := [([9,17,19], 1)]
theorem eval_atom1512 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1512 = ((g 9) * (g 17) * (g 19)) := by
  norm_num [atom1512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1512_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52712801442000 : Int) atom1512) := by
  rw [SparsePolynomial.eval_scale, eval_atom1512]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1513 : SparsePolynomial.Poly := [([9,17,20], 1)]
theorem eval_atom1513 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1513 = ((g 9) * (g 17) * (g 20)) := by
  norm_num [atom1513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1513_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58566148880400 : Int) atom1513) := by
  rw [SparsePolynomial.eval_scale, eval_atom1513]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1514 : SparsePolynomial.Poly := [([9,18,18], 1)]
theorem eval_atom1514 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1514 = ((g 9) * (g 18) * (g 18)) := by
  norm_num [atom1514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1514_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28394930554200 : Int) atom1514) := by
  rw [SparsePolynomial.eval_scale, eval_atom1514]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1515 : SparsePolynomial.Poly := [([9,18,19], 1)]
theorem eval_atom1515 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1515 = ((g 9) * (g 18) * (g 19)) := by
  norm_num [atom1515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1515_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36513604071000 : Int) atom1515) := by
  rw [SparsePolynomial.eval_scale, eval_atom1515]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1516 : SparsePolynomial.Poly := [([9,18,20], 1)]
theorem eval_atom1516 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1516 = ((g 9) * (g 18) * (g 20)) := by
  norm_num [atom1516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1516_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44758527817500 : Int) atom1516) := by
  rw [SparsePolynomial.eval_scale, eval_atom1516]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1517 : SparsePolynomial.Poly := [([9,19,19], 1)]
theorem eval_atom1517 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1517 = ((g 9) * (g 19) * (g 19)) := by
  norm_num [atom1517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1517_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3308751684000 : Int) atom1517) := by
  rw [SparsePolynomial.eval_scale, eval_atom1517]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1518 : SparsePolynomial.Poly := [([9,19,20], 1)]
theorem eval_atom1518 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1518 = ((g 9) * (g 19) * (g 20)) := by
  norm_num [atom1518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1518_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15671181626100 : Int) atom1518) := by
  rw [SparsePolynomial.eval_scale, eval_atom1518]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1519 : SparsePolynomial.Poly := [([9,20,20], 1)]
theorem eval_atom1519 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1519 = ((g 9) * (g 20) * (g 20)) := by
  norm_num [atom1519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1519_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8870673060900 : Int) atom1519) := by
  rw [SparsePolynomial.eval_scale, eval_atom1519]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1520 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom1520 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1520 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom1520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1520_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (597600864000 : Int) atom1520) := by
  rw [SparsePolynomial.eval_scale, eval_atom1520]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1521 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom1521 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1521 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom1521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1521_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1521) := by
  rw [SparsePolynomial.eval_scale, eval_atom1521]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1522 : SparsePolynomial.Poly := [([10,10,15], 1)]
theorem eval_atom1522 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1522 = ((g 10) * (g 10) * (g 15)) := by
  norm_num [atom1522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1522_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3075590700000 : Int) atom1522) := by
  rw [SparsePolynomial.eval_scale, eval_atom1522]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1523 : SparsePolynomial.Poly := [([10,10,17], 1)]
theorem eval_atom1523 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1523 = ((g 10) * (g 10) * (g 17)) := by
  norm_num [atom1523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1523_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2234314202400 : Int) atom1523) := by
  rw [SparsePolynomial.eval_scale, eval_atom1523]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1524 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom1524 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1524 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom1524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1524_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (938442758400 : Int) atom1524) := by
  rw [SparsePolynomial.eval_scale, eval_atom1524]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1525 : SparsePolynomial.Poly := [([10,11,13], 1)]
theorem eval_atom1525 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1525 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom1525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1525_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1525) := by
  rw [SparsePolynomial.eval_scale, eval_atom1525]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1526 : SparsePolynomial.Poly := [([10,11,14], 1)]
theorem eval_atom1526 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1526 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom1526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1526_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1526) := by
  rw [SparsePolynomial.eval_scale, eval_atom1526]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1527 : SparsePolynomial.Poly := [([10,11,15], 1)]
theorem eval_atom1527 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1527 = ((g 10) * (g 11) * (g 15)) := by
  norm_num [atom1527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1527_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5701373284320 : Int) atom1527) := by
  rw [SparsePolynomial.eval_scale, eval_atom1527]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1528 : SparsePolynomial.Poly := [([10,11,17], 1)]
theorem eval_atom1528 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1528 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom1528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1528_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10571867661600 : Int) atom1528) := by
  rw [SparsePolynomial.eval_scale, eval_atom1528]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1529 : SparsePolynomial.Poly := [([10,11,18], 1)]
theorem eval_atom1529 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1529 = ((g 10) * (g 11) * (g 18)) := by
  norm_num [atom1529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1529_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1529) := by
  rw [SparsePolynomial.eval_scale, eval_atom1529]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1530 : SparsePolynomial.Poly := [([10,11,19], 1)]
theorem eval_atom1530 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1530 = ((g 10) * (g 11) * (g 19)) := by
  norm_num [atom1530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1530_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1530) := by
  rw [SparsePolynomial.eval_scale, eval_atom1530]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1531 : SparsePolynomial.Poly := [([10,11,20], 1)]
theorem eval_atom1531 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1531 = ((g 10) * (g 11) * (g 20)) := by
  norm_num [atom1531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1531_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1531) := by
  rw [SparsePolynomial.eval_scale, eval_atom1531]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1532 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom1532 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1532 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom1532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1532_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1365622675200 : Int) atom1532) := by
  rw [SparsePolynomial.eval_scale, eval_atom1532]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1533 : SparsePolynomial.Poly := [([10,12,13], 1)]
theorem eval_atom1533 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1533 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom1533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1533_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2990259417600 : Int) atom1533) := by
  rw [SparsePolynomial.eval_scale, eval_atom1533]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1534 : SparsePolynomial.Poly := [([10,12,14], 1)]
theorem eval_atom1534 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1534 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom1534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1534_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3676453401600 : Int) atom1534) := by
  rw [SparsePolynomial.eval_scale, eval_atom1534]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1535 : SparsePolynomial.Poly := [([10,12,15], 1)]
theorem eval_atom1535 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1535 = ((g 10) * (g 12) * (g 15)) := by
  norm_num [atom1535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1535_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3338277354720 : Int) atom1535) := by
  rw [SparsePolynomial.eval_scale, eval_atom1535]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block020 : SparsePolynomial.Poly := [([9,9,17], 182739160800), ([9,10,10], 770276908800), ([9,10,13], 427179916800), ([9,10,14], 854359833600), ([9,10,15], 5669444229120), ([9,10,17], 6132165580800), ([9,10,18], 5786258284800), ([9,10,19], 11171238059520), ([9,10,20], 17391151612800), ([9,11,11], 1533788524800), ([9,11,12], 1876885516800), ([9,11,13], 2563079500800), ([9,11,14], 3249273484800), ([9,11,15], 6681901564800), ([9,11,16], 1017686224800), ([9,11,17], 12075930115200), ([9,11,18], 10740378448800), ([9,11,19], 20105092879200), ([9,11,20], 31025632780800), ([9,12,12], 3074342342400), ([9,12,13], 6498546969600), ([9,12,14], 7275589171200), ([9,12,15], 8588646595200), ([9,12,16], 6994941380000), ([9,12,17], 18707359395200), ([9,12,18], 19393808039200), ([9,12,19], 29075845864800), ([9,12,20], 40801239259200), ([9,13,13], 5863944096000), ([9,13,14], 11257079040000), ([9,13,15], 13909039300800), ([9,13,16], 13518234338400), ([9,13,17], 29696485795200), ([9,13,18], 32840704461600), ([9,13,19], 37111606192800), ([9,13,20], 55562141678400), ([9,14,14], 10101226464000), ([9,14,15], 19117589904000), ([9,14,16], 19922377860000), ([9,14,17], 42879142051200), ([9,14,18], 48700483725600), ([9,14,19], 49598093109600), ([9,14,20], 74906046734400), ([9,15,15], 16795322611200), ([9,15,16], 35735021557200), ([9,15,17], 64884545510400), ([9,15,18], 69986611724400), ([9,15,19], 53647060446000), ([9,15,20], 84256708258800), ([9,16,16], 14605687272960), ([9,16,17], 55660876311600), ([9,16,18], 65795220880200), ([9,16,19], 48673825250400), ([9,16,20], 66408854078700), ([9,17,17], 41744447539200), ([9,17,18], 76111510784400), ([9,17,19], 52712801442000), ([9,17,20], 58566148880400), ([9,18,18], 28394930554200), ([9,18,19], 36513604071000), ([9,18,20], 44758527817500), ([9,19,19], 3308751684000), ([9,19,20], 15671181626100), ([9,20,20], 8870673060900), ([10,10,10], 597600864000), ([10,10,11], 427179916800), ([10,10,15], 3075590700000), ([10,10,17], 2234314202400), ([10,11,11], 938442758400), ([10,11,13], 427179916800), ([10,11,14], 854359833600), ([10,11,15], 5701373284320), ([10,11,17], 10571867661600), ([10,11,18], 5786258284800), ([10,11,19], 11171238059520), ([10,11,20], 17391151612800), ([10,12,12], 1365622675200), ([10,12,13], 2990259417600), ([10,12,14], 3676453401600), ([10,12,15], 3338277354720)]
theorem block020_data : block020 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (182739160800 : Int) atom1456) (SparsePolynomial.scale (770276908800 : Int) atom1457)) (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1458) (SparsePolynomial.merge (SparsePolynomial.scale (854359833600 : Int) atom1459) (SparsePolynomial.scale (5669444229120 : Int) atom1460)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6132165580800 : Int) atom1461) (SparsePolynomial.scale (5786258284800 : Int) atom1462)) (SparsePolynomial.merge (SparsePolynomial.scale (11171238059520 : Int) atom1463) (SparsePolynomial.merge (SparsePolynomial.scale (17391151612800 : Int) atom1464) (SparsePolynomial.scale (1533788524800 : Int) atom1465))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1876885516800 : Int) atom1466) (SparsePolynomial.scale (2563079500800 : Int) atom1467)) (SparsePolynomial.merge (SparsePolynomial.scale (3249273484800 : Int) atom1468) (SparsePolynomial.merge (SparsePolynomial.scale (6681901564800 : Int) atom1469) (SparsePolynomial.scale (1017686224800 : Int) atom1470)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12075930115200 : Int) atom1471) (SparsePolynomial.scale (10740378448800 : Int) atom1472)) (SparsePolynomial.merge (SparsePolynomial.scale (20105092879200 : Int) atom1473) (SparsePolynomial.merge (SparsePolynomial.scale (31025632780800 : Int) atom1474) (SparsePolynomial.scale (3074342342400 : Int) atom1475)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6498546969600 : Int) atom1476) (SparsePolynomial.scale (7275589171200 : Int) atom1477)) (SparsePolynomial.merge (SparsePolynomial.scale (8588646595200 : Int) atom1478) (SparsePolynomial.merge (SparsePolynomial.scale (6994941380000 : Int) atom1479) (SparsePolynomial.scale (18707359395200 : Int) atom1480)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19393808039200 : Int) atom1481) (SparsePolynomial.scale (29075845864800 : Int) atom1482)) (SparsePolynomial.merge (SparsePolynomial.scale (40801239259200 : Int) atom1483) (SparsePolynomial.merge (SparsePolynomial.scale (5863944096000 : Int) atom1484) (SparsePolynomial.scale (11257079040000 : Int) atom1485))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13909039300800 : Int) atom1486) (SparsePolynomial.scale (13518234338400 : Int) atom1487)) (SparsePolynomial.merge (SparsePolynomial.scale (29696485795200 : Int) atom1488) (SparsePolynomial.merge (SparsePolynomial.scale (32840704461600 : Int) atom1489) (SparsePolynomial.scale (37111606192800 : Int) atom1490)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55562141678400 : Int) atom1491) (SparsePolynomial.scale (10101226464000 : Int) atom1492)) (SparsePolynomial.merge (SparsePolynomial.scale (19117589904000 : Int) atom1493) (SparsePolynomial.merge (SparsePolynomial.scale (19922377860000 : Int) atom1494) (SparsePolynomial.scale (42879142051200 : Int) atom1495))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48700483725600 : Int) atom1496) (SparsePolynomial.scale (49598093109600 : Int) atom1497)) (SparsePolynomial.merge (SparsePolynomial.scale (74906046734400 : Int) atom1498) (SparsePolynomial.merge (SparsePolynomial.scale (16795322611200 : Int) atom1499) (SparsePolynomial.scale (35735021557200 : Int) atom1500)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64884545510400 : Int) atom1501) (SparsePolynomial.scale (69986611724400 : Int) atom1502)) (SparsePolynomial.merge (SparsePolynomial.scale (53647060446000 : Int) atom1503) (SparsePolynomial.merge (SparsePolynomial.scale (84256708258800 : Int) atom1504) (SparsePolynomial.scale (14605687272960 : Int) atom1505))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55660876311600 : Int) atom1506) (SparsePolynomial.scale (65795220880200 : Int) atom1507)) (SparsePolynomial.merge (SparsePolynomial.scale (48673825250400 : Int) atom1508) (SparsePolynomial.merge (SparsePolynomial.scale (66408854078700 : Int) atom1509) (SparsePolynomial.scale (41744447539200 : Int) atom1510)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (76111510784400 : Int) atom1511) (SparsePolynomial.scale (52712801442000 : Int) atom1512)) (SparsePolynomial.merge (SparsePolynomial.scale (58566148880400 : Int) atom1513) (SparsePolynomial.merge (SparsePolynomial.scale (28394930554200 : Int) atom1514) (SparsePolynomial.scale (36513604071000 : Int) atom1515)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (44758527817500 : Int) atom1516) (SparsePolynomial.scale (3308751684000 : Int) atom1517)) (SparsePolynomial.merge (SparsePolynomial.scale (15671181626100 : Int) atom1518) (SparsePolynomial.merge (SparsePolynomial.scale (8870673060900 : Int) atom1519) (SparsePolynomial.scale (597600864000 : Int) atom1520)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1521) (SparsePolynomial.scale (3075590700000 : Int) atom1522)) (SparsePolynomial.merge (SparsePolynomial.scale (2234314202400 : Int) atom1523) (SparsePolynomial.merge (SparsePolynomial.scale (938442758400 : Int) atom1524) (SparsePolynomial.scale (427179916800 : Int) atom1525))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (854359833600 : Int) atom1526) (SparsePolynomial.scale (5701373284320 : Int) atom1527)) (SparsePolynomial.merge (SparsePolynomial.scale (10571867661600 : Int) atom1528) (SparsePolynomial.merge (SparsePolynomial.scale (5786258284800 : Int) atom1529) (SparsePolynomial.scale (11171238059520 : Int) atom1530)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17391151612800 : Int) atom1531) (SparsePolynomial.scale (1365622675200 : Int) atom1532)) (SparsePolynomial.merge (SparsePolynomial.scale (2990259417600 : Int) atom1533) (SparsePolynomial.merge (SparsePolynomial.scale (3676453401600 : Int) atom1534) (SparsePolynomial.scale (3338277354720 : Int) atom1535)))))))) := by decide +kernel
theorem block020_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block020 := by
  rw [block020_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1456_nonneg g hg hA hB) (atom1457_nonneg g hg hA hB)) (add_nonneg (atom1458_nonneg g hg hA hB) (add_nonneg (atom1459_nonneg g hg hA hB) (atom1460_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1461_nonneg g hg hA hB) (atom1462_nonneg g hg hA hB)) (add_nonneg (atom1463_nonneg g hg hA hB) (add_nonneg (atom1464_nonneg g hg hA hB) (atom1465_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1466_nonneg g hg hA hB) (atom1467_nonneg g hg hA hB)) (add_nonneg (atom1468_nonneg g hg hA hB) (add_nonneg (atom1469_nonneg g hg hA hB) (atom1470_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1471_nonneg g hg hA hB) (atom1472_nonneg g hg hA hB)) (add_nonneg (atom1473_nonneg g hg hA hB) (add_nonneg (atom1474_nonneg g hg hA hB) (atom1475_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1476_nonneg g hg hA hB) (atom1477_nonneg g hg hA hB)) (add_nonneg (atom1478_nonneg g hg hA hB) (add_nonneg (atom1479_nonneg g hg hA hB) (atom1480_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1481_nonneg g hg hA hB) (atom1482_nonneg g hg hA hB)) (add_nonneg (atom1483_nonneg g hg hA hB) (add_nonneg (atom1484_nonneg g hg hA hB) (atom1485_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1486_nonneg g hg hA hB) (atom1487_nonneg g hg hA hB)) (add_nonneg (atom1488_nonneg g hg hA hB) (add_nonneg (atom1489_nonneg g hg hA hB) (atom1490_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1491_nonneg g hg hA hB) (atom1492_nonneg g hg hA hB)) (add_nonneg (atom1493_nonneg g hg hA hB) (add_nonneg (atom1494_nonneg g hg hA hB) (atom1495_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1496_nonneg g hg hA hB) (atom1497_nonneg g hg hA hB)) (add_nonneg (atom1498_nonneg g hg hA hB) (add_nonneg (atom1499_nonneg g hg hA hB) (atom1500_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1501_nonneg g hg hA hB) (atom1502_nonneg g hg hA hB)) (add_nonneg (atom1503_nonneg g hg hA hB) (add_nonneg (atom1504_nonneg g hg hA hB) (atom1505_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1506_nonneg g hg hA hB) (atom1507_nonneg g hg hA hB)) (add_nonneg (atom1508_nonneg g hg hA hB) (add_nonneg (atom1509_nonneg g hg hA hB) (atom1510_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1511_nonneg g hg hA hB) (atom1512_nonneg g hg hA hB)) (add_nonneg (atom1513_nonneg g hg hA hB) (add_nonneg (atom1514_nonneg g hg hA hB) (atom1515_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1516_nonneg g hg hA hB) (atom1517_nonneg g hg hA hB)) (add_nonneg (atom1518_nonneg g hg hA hB) (add_nonneg (atom1519_nonneg g hg hA hB) (atom1520_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1521_nonneg g hg hA hB) (atom1522_nonneg g hg hA hB)) (add_nonneg (atom1523_nonneg g hg hA hB) (add_nonneg (atom1524_nonneg g hg hA hB) (atom1525_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1526_nonneg g hg hA hB) (atom1527_nonneg g hg hA hB)) (add_nonneg (atom1528_nonneg g hg hA hB) (add_nonneg (atom1529_nonneg g hg hA hB) (atom1530_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1531_nonneg g hg hA hB) (atom1532_nonneg g hg hA hB)) (add_nonneg (atom1533_nonneg g hg hA hB) (add_nonneg (atom1534_nonneg g hg hA hB) (atom1535_nonneg g hg hA hB))))))))

end APPT.Finite21
