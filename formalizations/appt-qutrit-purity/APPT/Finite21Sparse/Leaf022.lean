import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1616 : SparsePolynomial.Poly := [([11,18,19], 1)]
theorem eval_atom1616 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1616 = ((g 11) * (g 18) * (g 19)) := by
  norm_num [atom1616, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1616_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58329956563200 : Int) atom1616) := by
  rw [SparsePolynomial.eval_scale, eval_atom1616]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1617 : SparsePolynomial.Poly := [([11,18,20], 1)]
theorem eval_atom1617 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1617 = ((g 11) * (g 18) * (g 20)) := by
  norm_num [atom1617, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1617_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71135158752000 : Int) atom1617) := by
  rw [SparsePolynomial.eval_scale, eval_atom1617]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1618 : SparsePolynomial.Poly := [([11,19,19], 1)]
theorem eval_atom1618 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1618 = ((g 11) * (g 19) * (g 19)) := by
  norm_num [atom1618, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1618_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16986153139200 : Int) atom1618) := by
  rw [SparsePolynomial.eval_scale, eval_atom1618]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1619 : SparsePolynomial.Poly := [([11,19,20], 1)]
theorem eval_atom1619 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1619 = ((g 11) * (g 19) * (g 20)) := by
  norm_num [atom1619, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1619_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48554288496000 : Int) atom1619) := by
  rw [SparsePolynomial.eval_scale, eval_atom1619]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1620 : SparsePolynomial.Poly := [([11,20,20], 1)]
theorem eval_atom1620 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1620 = ((g 11) * (g 20) * (g 20)) := by
  norm_num [atom1620, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1620_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27477786268800 : Int) atom1620) := by
  rw [SparsePolynomial.eval_scale, eval_atom1620]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1621 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom1621 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1621 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom1621, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1621_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (142393305600 : Int) atom1621) := by
  rw [SparsePolynomial.eval_scale, eval_atom1621]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1622 : SparsePolynomial.Poly := [([12,12,17], 1)]
theorem eval_atom1622 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1622 = ((g 12) * (g 12) * (g 17)) := by
  norm_num [atom1622, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1622_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3961249152000 : Int) atom1622) := by
  rw [SparsePolynomial.eval_scale, eval_atom1622]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1623 : SparsePolynomial.Poly := [([12,12,18], 1)]
theorem eval_atom1623 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1623 = ((g 12) * (g 12) * (g 18)) := by
  norm_num [atom1623, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1623_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (657701004800 : Int) atom1623) := by
  rw [SparsePolynomial.eval_scale, eval_atom1623]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1624 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom1624 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1624 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom1624, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1624_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (731019801600 : Int) atom1624) := by
  rw [SparsePolynomial.eval_scale, eval_atom1624]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1625 : SparsePolynomial.Poly := [([12,13,14], 1)]
theorem eval_atom1625 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1625 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom1625, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1625_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (718685798400 : Int) atom1625) := by
  rw [SparsePolynomial.eval_scale, eval_atom1625]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1626 : SparsePolynomial.Poly := [([12,13,16], 1)]
theorem eval_atom1626 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1626 = ((g 12) * (g 13) * (g 16)) := by
  norm_num [atom1626, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1626_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (781859212800 : Int) atom1626) := by
  rw [SparsePolynomial.eval_scale, eval_atom1626]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1627 : SparsePolynomial.Poly := [([12,13,17], 1)]
theorem eval_atom1627 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1627 = ((g 12) * (g 13) * (g 17)) := by
  norm_num [atom1627, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1627_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16022245108800 : Int) atom1627) := by
  rw [SparsePolynomial.eval_scale, eval_atom1627]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1628 : SparsePolynomial.Poly := [([12,13,18], 1)]
theorem eval_atom1628 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1628 = ((g 12) * (g 13) * (g 18)) := by
  norm_num [atom1628, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1628_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13551194686400 : Int) atom1628) := by
  rw [SparsePolynomial.eval_scale, eval_atom1628]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1629 : SparsePolynomial.Poly := [([12,13,19], 1)]
theorem eval_atom1629 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1629 = ((g 12) * (g 13) * (g 19)) := by
  norm_num [atom1629, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1629_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11776027622400 : Int) atom1629) := by
  rw [SparsePolynomial.eval_scale, eval_atom1629]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1630 : SparsePolynomial.Poly := [([12,13,20], 1)]
theorem eval_atom1630 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1630 = ((g 12) * (g 13) * (g 20)) := by
  norm_num [atom1630, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1630_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24502199198400 : Int) atom1630) := by
  rw [SparsePolynomial.eval_scale, eval_atom1630]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1631 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom1631 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1631 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom1631, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1631_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3414217766400 : Int) atom1631) := by
  rw [SparsePolynomial.eval_scale, eval_atom1631]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1632 : SparsePolynomial.Poly := [([12,14,16], 1)]
theorem eval_atom1632 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1632 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom1632, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1632_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1274989228800 : Int) atom1632) := by
  rw [SparsePolynomial.eval_scale, eval_atom1632]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1633 : SparsePolynomial.Poly := [([12,14,17], 1)]
theorem eval_atom1633 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1633 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom1633, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1633_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25932352051200 : Int) atom1633) := by
  rw [SparsePolynomial.eval_scale, eval_atom1633]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1634 : SparsePolynomial.Poly := [([12,14,18], 1)]
theorem eval_atom1634 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1634 = ((g 12) * (g 14) * (g 18)) := by
  norm_num [atom1634, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1634_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27709905507200 : Int) atom1634) := by
  rw [SparsePolynomial.eval_scale, eval_atom1634]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1635 : SparsePolynomial.Poly := [([12,14,19], 1)]
theorem eval_atom1635 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1635 = ((g 12) * (g 14) * (g 19)) := by
  norm_num [atom1635, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1635_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27473854060800 : Int) atom1635) := by
  rw [SparsePolynomial.eval_scale, eval_atom1635]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1636 : SparsePolynomial.Poly := [([12,14,20], 1)]
theorem eval_atom1636 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1636 = ((g 12) * (g 14) * (g 20)) := by
  norm_num [atom1636, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1636_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53106823627200 : Int) atom1636) := by
  rw [SparsePolynomial.eval_scale, eval_atom1636]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1637 : SparsePolynomial.Poly := [([12,15,15], 1)]
theorem eval_atom1637 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1637 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom1637, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1637_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6357299110400 : Int) atom1637) := by
  rw [SparsePolynomial.eval_scale, eval_atom1637]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1638 : SparsePolynomial.Poly := [([12,15,16], 1)]
theorem eval_atom1638 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1638 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom1638, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1638_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19520661753600 : Int) atom1638) := by
  rw [SparsePolynomial.eval_scale, eval_atom1638]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1639 : SparsePolynomial.Poly := [([12,15,17], 1)]
theorem eval_atom1639 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1639 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom1639, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1639_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54017265971200 : Int) atom1639) := by
  rw [SparsePolynomial.eval_scale, eval_atom1639]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1640 : SparsePolynomial.Poly := [([12,15,18], 1)]
theorem eval_atom1640 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1640 = ((g 12) * (g 15) * (g 18)) := by
  norm_num [atom1640, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1640_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60723048870400 : Int) atom1640) := by
  rw [SparsePolynomial.eval_scale, eval_atom1640]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1641 : SparsePolynomial.Poly := [([12,15,19], 1)]
theorem eval_atom1641 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1641 = ((g 12) * (g 15) * (g 19)) := by
  norm_num [atom1641, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1641_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48904332915200 : Int) atom1641) := by
  rw [SparsePolynomial.eval_scale, eval_atom1641]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1642 : SparsePolynomial.Poly := [([12,15,20], 1)]
theorem eval_atom1642 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1642 = ((g 12) * (g 15) * (g 20)) := by
  norm_num [atom1642, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1642_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82971805996800 : Int) atom1642) := by
  rw [SparsePolynomial.eval_scale, eval_atom1642]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1643 : SparsePolynomial.Poly := [([12,16,16], 1)]
theorem eval_atom1643 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1643 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom1643, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1643_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7890507752960 : Int) atom1643) := by
  rw [SparsePolynomial.eval_scale, eval_atom1643]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1644 : SparsePolynomial.Poly := [([12,16,17], 1)]
theorem eval_atom1644 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1644 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom1644, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1644_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48082095084800 : Int) atom1644) := by
  rw [SparsePolynomial.eval_scale, eval_atom1644]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1645 : SparsePolynomial.Poly := [([12,16,18], 1)]
theorem eval_atom1645 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1645 = ((g 12) * (g 16) * (g 18)) := by
  norm_num [atom1645, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1645_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63896669200000 : Int) atom1645) := by
  rw [SparsePolynomial.eval_scale, eval_atom1645]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1646 : SparsePolynomial.Poly := [([12,16,19], 1)]
theorem eval_atom1646 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1646 = ((g 12) * (g 16) * (g 19)) := by
  norm_num [atom1646, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1646_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55239224230400 : Int) atom1646) := by
  rw [SparsePolynomial.eval_scale, eval_atom1646]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1647 : SparsePolynomial.Poly := [([12,16,20], 1)]
theorem eval_atom1647 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1647 = ((g 12) * (g 16) * (g 20)) := by
  norm_num [atom1647, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1647_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78568808472000 : Int) atom1647) := by
  rw [SparsePolynomial.eval_scale, eval_atom1647]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1648 : SparsePolynomial.Poly := [([12,17,17], 1)]
theorem eval_atom1648 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1648 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom1648, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1648_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39256609548800 : Int) atom1648) := by
  rw [SparsePolynomial.eval_scale, eval_atom1648]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1649 : SparsePolynomial.Poly := [([12,17,18], 1)]
theorem eval_atom1649 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1649 = ((g 12) * (g 17) * (g 18)) := by
  norm_num [atom1649, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1649_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (80549880678400 : Int) atom1649) := by
  rw [SparsePolynomial.eval_scale, eval_atom1649]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1650 : SparsePolynomial.Poly := [([12,17,19], 1)]
theorem eval_atom1650 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1650 = ((g 12) * (g 17) * (g 19)) := by
  norm_num [atom1650, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1650_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69215540800000 : Int) atom1650) := by
  rw [SparsePolynomial.eval_scale, eval_atom1650]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1651 : SparsePolynomial.Poly := [([12,17,20], 1)]
theorem eval_atom1651 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1651 = ((g 12) * (g 17) * (g 20)) := by
  norm_num [atom1651, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1651_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88196267756800 : Int) atom1651) := by
  rw [SparsePolynomial.eval_scale, eval_atom1651]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1652 : SparsePolynomial.Poly := [([12,18,18], 1)]
theorem eval_atom1652 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1652 = ((g 12) * (g 18) * (g 18)) := by
  norm_num [atom1652, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1652_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35739932211200 : Int) atom1652) := by
  rw [SparsePolynomial.eval_scale, eval_atom1652]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1653 : SparsePolynomial.Poly := [([12,18,19], 1)]
theorem eval_atom1653 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1653 = ((g 12) * (g 18) * (g 19)) := by
  norm_num [atom1653, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1653_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (67106442681600 : Int) atom1653) := by
  rw [SparsePolynomial.eval_scale, eval_atom1653]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1654 : SparsePolynomial.Poly := [([12,18,20], 1)]
theorem eval_atom1654 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1654 = ((g 12) * (g 18) * (g 20)) := by
  norm_num [atom1654, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1654_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90606689488000 : Int) atom1654) := by
  rw [SparsePolynomial.eval_scale, eval_atom1654]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1655 : SparsePolynomial.Poly := [([12,19,19], 1)]
theorem eval_atom1655 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1655 = ((g 12) * (g 19) * (g 19)) := by
  norm_num [atom1655, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1655_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25516823091200 : Int) atom1655) := by
  rw [SparsePolynomial.eval_scale, eval_atom1655]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1656 : SparsePolynomial.Poly := [([12,19,20], 1)]
theorem eval_atom1656 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1656 = ((g 12) * (g 19) * (g 20)) := by
  norm_num [atom1656, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1656_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77437241660800 : Int) atom1656) := by
  rw [SparsePolynomial.eval_scale, eval_atom1656]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1657 : SparsePolynomial.Poly := [([12,20,20], 1)]
theorem eval_atom1657 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1657 = ((g 12) * (g 20) * (g 20)) := by
  norm_num [atom1657, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1657_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47533761553600 : Int) atom1657) := by
  rw [SparsePolynomial.eval_scale, eval_atom1657]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1658 : SparsePolynomial.Poly := [([13,13,13], 1)]
theorem eval_atom1658 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1658 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom1658, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1658_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (390177907200 : Int) atom1658) := by
  rw [SparsePolynomial.eval_scale, eval_atom1658]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1659 : SparsePolynomial.Poly := [([13,13,17], 1)]
theorem eval_atom1659 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1659 = ((g 13) * (g 13) * (g 17)) := by
  norm_num [atom1659, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1659_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7496187508800 : Int) atom1659) := by
  rw [SparsePolynomial.eval_scale, eval_atom1659]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1660 : SparsePolynomial.Poly := [([13,13,18], 1)]
theorem eval_atom1660 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1660 = ((g 13) * (g 13) * (g 18)) := by
  norm_num [atom1660, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1660_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6223620657600 : Int) atom1660) := by
  rw [SparsePolynomial.eval_scale, eval_atom1660]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661 : SparsePolynomial.Poly := [([13,13,20], 1)]
theorem eval_atom1661 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1661 = ((g 13) * (g 13) * (g 20)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1661_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6958414296000 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1662 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom1662 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1662 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom1662, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1662_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1828838131200 : Int) atom1662) := by
  rw [SparsePolynomial.eval_scale, eval_atom1662]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1663 : SparsePolynomial.Poly := [([13,14,16], 1)]
theorem eval_atom1663 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1663 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom1663, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1663_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2672152588800 : Int) atom1663) := by
  rw [SparsePolynomial.eval_scale, eval_atom1663]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1664 : SparsePolynomial.Poly := [([13,14,17], 1)]
theorem eval_atom1664 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1664 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom1664, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1664_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28714425307200 : Int) atom1664) := by
  rw [SparsePolynomial.eval_scale, eval_atom1664]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1665 : SparsePolynomial.Poly := [([13,14,18], 1)]
theorem eval_atom1665 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1665 = ((g 13) * (g 14) * (g 18)) := by
  norm_num [atom1665, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1665_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31318438795200 : Int) atom1665) := by
  rw [SparsePolynomial.eval_scale, eval_atom1665]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1666 : SparsePolynomial.Poly := [([13,14,19], 1)]
theorem eval_atom1666 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1666 = ((g 13) * (g 14) * (g 19)) := by
  norm_num [atom1666, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1666_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20764754611200 : Int) atom1666) := by
  rw [SparsePolynomial.eval_scale, eval_atom1666]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1667 : SparsePolynomial.Poly := [([13,14,20], 1)]
theorem eval_atom1667 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1667 = ((g 13) * (g 14) * (g 20)) := by
  norm_num [atom1667, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1667_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47303583076800 : Int) atom1667) := by
  rw [SparsePolynomial.eval_scale, eval_atom1667]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1668 : SparsePolynomial.Poly := [([13,15,15], 1)]
theorem eval_atom1668 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1668 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom1668, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1668_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3550208205600 : Int) atom1668) := by
  rw [SparsePolynomial.eval_scale, eval_atom1668]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1669 : SparsePolynomial.Poly := [([13,15,16], 1)]
theorem eval_atom1669 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1669 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom1669, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1669_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14159602504800 : Int) atom1669) := by
  rw [SparsePolynomial.eval_scale, eval_atom1669]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1670 : SparsePolynomial.Poly := [([13,15,17], 1)]
theorem eval_atom1670 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1670 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom1670, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1670_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50540795877600 : Int) atom1670) := by
  rw [SparsePolynomial.eval_scale, eval_atom1670]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1671 : SparsePolynomial.Poly := [([13,15,18], 1)]
theorem eval_atom1671 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1671 = ((g 13) * (g 15) * (g 18)) := by
  norm_num [atom1671, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1671_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58714949336400 : Int) atom1671) := by
  rw [SparsePolynomial.eval_scale, eval_atom1671]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1672 : SparsePolynomial.Poly := [([13,15,19], 1)]
theorem eval_atom1672 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1672 = ((g 13) * (g 15) * (g 19)) := by
  norm_num [atom1672, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1672_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44621368840800 : Int) atom1672) := by
  rw [SparsePolynomial.eval_scale, eval_atom1672]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1673 : SparsePolynomial.Poly := [([13,15,20], 1)]
theorem eval_atom1673 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1673 = ((g 13) * (g 15) * (g 20)) := by
  norm_num [atom1673, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1673_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82584805073400 : Int) atom1673) := by
  rw [SparsePolynomial.eval_scale, eval_atom1673]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1674 : SparsePolynomial.Poly := [([13,16,16], 1)]
theorem eval_atom1674 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1674 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom1674, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1674_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5924850140160 : Int) atom1674) := by
  rw [SparsePolynomial.eval_scale, eval_atom1674]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1675 : SparsePolynomial.Poly := [([13,16,17], 1)]
theorem eval_atom1675 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1675 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom1675, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1675_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46603049565600 : Int) atom1675) := by
  rw [SparsePolynomial.eval_scale, eval_atom1675]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1676 : SparsePolynomial.Poly := [([13,16,18], 1)]
theorem eval_atom1676 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1676 = ((g 13) * (g 16) * (g 18)) := by
  norm_num [atom1676, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1676_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64561905414000 : Int) atom1676) := by
  rw [SparsePolynomial.eval_scale, eval_atom1676]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1677 : SparsePolynomial.Poly := [([13,16,19], 1)]
theorem eval_atom1677 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1677 = ((g 13) * (g 16) * (g 19)) := by
  norm_num [atom1677, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1677_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58431178094400 : Int) atom1677) := by
  rw [SparsePolynomial.eval_scale, eval_atom1677]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1678 : SparsePolynomial.Poly := [([13,16,20], 1)]
theorem eval_atom1678 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1678 = ((g 13) * (g 16) * (g 20)) := by
  norm_num [atom1678, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1678_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83751050082600 : Int) atom1678) := by
  rw [SparsePolynomial.eval_scale, eval_atom1678]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1679 : SparsePolynomial.Poly := [([13,17,17], 1)]
theorem eval_atom1679 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1679 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom1679, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1679_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38700065779200 : Int) atom1679) := by
  rw [SparsePolynomial.eval_scale, eval_atom1679]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1680 : SparsePolynomial.Poly := [([13,17,18], 1)]
theorem eval_atom1680 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1680 = ((g 13) * (g 17) * (g 18)) := by
  norm_num [atom1680, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1680_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81441252748800 : Int) atom1680) := by
  rw [SparsePolynomial.eval_scale, eval_atom1680]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1681 : SparsePolynomial.Poly := [([13,17,19], 1)]
theorem eval_atom1681 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1681 = ((g 13) * (g 17) * (g 19)) := by
  norm_num [atom1681, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1681_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76619479413600 : Int) atom1681) := by
  rw [SparsePolynomial.eval_scale, eval_atom1681]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1682 : SparsePolynomial.Poly := [([13,17,20], 1)]
theorem eval_atom1682 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1682 = ((g 13) * (g 17) * (g 20)) := by
  norm_num [atom1682, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1682_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96041823897600 : Int) atom1682) := by
  rw [SparsePolynomial.eval_scale, eval_atom1682]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1683 : SparsePolynomial.Poly := [([13,18,18], 1)]
theorem eval_atom1683 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1683 = ((g 13) * (g 18) * (g 18)) := by
  norm_num [atom1683, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1683_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36760668134400 : Int) atom1683) := by
  rw [SparsePolynomial.eval_scale, eval_atom1683]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1684 : SparsePolynomial.Poly := [([13,18,19], 1)]
theorem eval_atom1684 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1684 = ((g 13) * (g 18) * (g 19)) := by
  norm_num [atom1684, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1684_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77891482429200 : Int) atom1684) := by
  rw [SparsePolynomial.eval_scale, eval_atom1684]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1685 : SparsePolynomial.Poly := [([13,18,20], 1)]
theorem eval_atom1685 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1685 = ((g 13) * (g 18) * (g 20)) := by
  norm_num [atom1685, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1685_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100837655654400 : Int) atom1685) := by
  rw [SparsePolynomial.eval_scale, eval_atom1685]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1686 : SparsePolynomial.Poly := [([13,19,19], 1)]
theorem eval_atom1686 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1686 = ((g 13) * (g 19) * (g 19)) := by
  norm_num [atom1686, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1686_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36725564548800 : Int) atom1686) := by
  rw [SparsePolynomial.eval_scale, eval_atom1686]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1687 : SparsePolynomial.Poly := [([13,19,20], 1)]
theorem eval_atom1687 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1687 = ((g 13) * (g 19) * (g 20)) := by
  norm_num [atom1687, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1687_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99336377640600 : Int) atom1687) := by
  rw [SparsePolynomial.eval_scale, eval_atom1687]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1688 : SparsePolynomial.Poly := [([13,20,20], 1)]
theorem eval_atom1688 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1688 = ((g 13) * (g 20) * (g 20)) := by
  norm_num [atom1688, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1688_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57215047680000 : Int) atom1688) := by
  rw [SparsePolynomial.eval_scale, eval_atom1688]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1689 : SparsePolynomial.Poly := [([14,14,14], 1)]
theorem eval_atom1689 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1689 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom1689, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1689_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1735780838400 : Int) atom1689) := by
  rw [SparsePolynomial.eval_scale, eval_atom1689]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690 : SparsePolynomial.Poly := [([14,14,17], 1)]
theorem eval_atom1690 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1690 = ((g 14) * (g 14) * (g 17)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1690_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13628959948800 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1691 : SparsePolynomial.Poly := [([14,14,18], 1)]
theorem eval_atom1691 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1691 = ((g 14) * (g 14) * (g 18)) := by
  norm_num [atom1691, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1691_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14833387699200 : Int) atom1691) := by
  rw [SparsePolynomial.eval_scale, eval_atom1691]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1692 : SparsePolynomial.Poly := [([14,14,19], 1)]
theorem eval_atom1692 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1692 = ((g 14) * (g 14) * (g 19)) := by
  norm_num [atom1692, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1692_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5586198912000 : Int) atom1692) := by
  rw [SparsePolynomial.eval_scale, eval_atom1692]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1693 : SparsePolynomial.Poly := [([14,14,20], 1)]
theorem eval_atom1693 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1693 = ((g 14) * (g 14) * (g 20)) := by
  norm_num [atom1693, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1693_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20249487820800 : Int) atom1693) := by
  rw [SparsePolynomial.eval_scale, eval_atom1693]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1694 : SparsePolynomial.Poly := [([14,15,15], 1)]
theorem eval_atom1694 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1694 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom1694, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1694_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (906549235200 : Int) atom1694) := by
  rw [SparsePolynomial.eval_scale, eval_atom1694]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1695 : SparsePolynomial.Poly := [([14,15,16], 1)]
theorem eval_atom1695 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1695 = ((g 14) * (g 15) * (g 16)) := by
  norm_num [atom1695, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1695_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9616380480000 : Int) atom1695) := by
  rw [SparsePolynomial.eval_scale, eval_atom1695]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block022 : SparsePolynomial.Poly := [([11,18,19], 58329956563200), ([11,18,20], 71135158752000), ([11,19,19], 16986153139200), ([11,19,20], 48554288496000), ([11,20,20], 27477786268800), ([12,12,12], 142393305600), ([12,12,17], 3961249152000), ([12,12,18], 657701004800), ([12,13,13], 731019801600), ([12,13,14], 718685798400), ([12,13,16], 781859212800), ([12,13,17], 16022245108800), ([12,13,18], 13551194686400), ([12,13,19], 11776027622400), ([12,13,20], 24502199198400), ([12,14,14], 3414217766400), ([12,14,16], 1274989228800), ([12,14,17], 25932352051200), ([12,14,18], 27709905507200), ([12,14,19], 27473854060800), ([12,14,20], 53106823627200), ([12,15,15], 6357299110400), ([12,15,16], 19520661753600), ([12,15,17], 54017265971200), ([12,15,18], 60723048870400), ([12,15,19], 48904332915200), ([12,15,20], 82971805996800), ([12,16,16], 7890507752960), ([12,16,17], 48082095084800), ([12,16,18], 63896669200000), ([12,16,19], 55239224230400), ([12,16,20], 78568808472000), ([12,17,17], 39256609548800), ([12,17,18], 80549880678400), ([12,17,19], 69215540800000), ([12,17,20], 88196267756800), ([12,18,18], 35739932211200), ([12,18,19], 67106442681600), ([12,18,20], 90606689488000), ([12,19,19], 25516823091200), ([12,19,20], 77437241660800), ([12,20,20], 47533761553600), ([13,13,13], 390177907200), ([13,13,17], 7496187508800), ([13,13,18], 6223620657600), ([13,13,20], 6958414296000), ([13,14,14], 1828838131200), ([13,14,16], 2672152588800), ([13,14,17], 28714425307200), ([13,14,18], 31318438795200), ([13,14,19], 20764754611200), ([13,14,20], 47303583076800), ([13,15,15], 3550208205600), ([13,15,16], 14159602504800), ([13,15,17], 50540795877600), ([13,15,18], 58714949336400), ([13,15,19], 44621368840800), ([13,15,20], 82584805073400), ([13,16,16], 5924850140160), ([13,16,17], 46603049565600), ([13,16,18], 64561905414000), ([13,16,19], 58431178094400), ([13,16,20], 83751050082600), ([13,17,17], 38700065779200), ([13,17,18], 81441252748800), ([13,17,19], 76619479413600), ([13,17,20], 96041823897600), ([13,18,18], 36760668134400), ([13,18,19], 77891482429200), ([13,18,20], 100837655654400), ([13,19,19], 36725564548800), ([13,19,20], 99336377640600), ([13,20,20], 57215047680000), ([14,14,14], 1735780838400), ([14,14,17], 13628959948800), ([14,14,18], 14833387699200), ([14,14,19], 5586198912000), ([14,14,20], 20249487820800), ([14,15,15], 906549235200), ([14,15,16], 9616380480000)]
theorem block022_data : block022 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (58329956563200 : Int) atom1616) (SparsePolynomial.scale (71135158752000 : Int) atom1617)) (SparsePolynomial.merge (SparsePolynomial.scale (16986153139200 : Int) atom1618) (SparsePolynomial.merge (SparsePolynomial.scale (48554288496000 : Int) atom1619) (SparsePolynomial.scale (27477786268800 : Int) atom1620)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142393305600 : Int) atom1621) (SparsePolynomial.scale (3961249152000 : Int) atom1622)) (SparsePolynomial.merge (SparsePolynomial.scale (657701004800 : Int) atom1623) (SparsePolynomial.merge (SparsePolynomial.scale (731019801600 : Int) atom1624) (SparsePolynomial.scale (718685798400 : Int) atom1625))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (781859212800 : Int) atom1626) (SparsePolynomial.scale (16022245108800 : Int) atom1627)) (SparsePolynomial.merge (SparsePolynomial.scale (13551194686400 : Int) atom1628) (SparsePolynomial.merge (SparsePolynomial.scale (11776027622400 : Int) atom1629) (SparsePolynomial.scale (24502199198400 : Int) atom1630)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3414217766400 : Int) atom1631) (SparsePolynomial.scale (1274989228800 : Int) atom1632)) (SparsePolynomial.merge (SparsePolynomial.scale (25932352051200 : Int) atom1633) (SparsePolynomial.merge (SparsePolynomial.scale (27709905507200 : Int) atom1634) (SparsePolynomial.scale (27473854060800 : Int) atom1635)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (53106823627200 : Int) atom1636) (SparsePolynomial.scale (6357299110400 : Int) atom1637)) (SparsePolynomial.merge (SparsePolynomial.scale (19520661753600 : Int) atom1638) (SparsePolynomial.merge (SparsePolynomial.scale (54017265971200 : Int) atom1639) (SparsePolynomial.scale (60723048870400 : Int) atom1640)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48904332915200 : Int) atom1641) (SparsePolynomial.scale (82971805996800 : Int) atom1642)) (SparsePolynomial.merge (SparsePolynomial.scale (7890507752960 : Int) atom1643) (SparsePolynomial.merge (SparsePolynomial.scale (48082095084800 : Int) atom1644) (SparsePolynomial.scale (63896669200000 : Int) atom1645))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55239224230400 : Int) atom1646) (SparsePolynomial.scale (78568808472000 : Int) atom1647)) (SparsePolynomial.merge (SparsePolynomial.scale (39256609548800 : Int) atom1648) (SparsePolynomial.merge (SparsePolynomial.scale (80549880678400 : Int) atom1649) (SparsePolynomial.scale (69215540800000 : Int) atom1650)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88196267756800 : Int) atom1651) (SparsePolynomial.scale (35739932211200 : Int) atom1652)) (SparsePolynomial.merge (SparsePolynomial.scale (67106442681600 : Int) atom1653) (SparsePolynomial.merge (SparsePolynomial.scale (90606689488000 : Int) atom1654) (SparsePolynomial.scale (25516823091200 : Int) atom1655))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (77437241660800 : Int) atom1656) (SparsePolynomial.scale (47533761553600 : Int) atom1657)) (SparsePolynomial.merge (SparsePolynomial.scale (390177907200 : Int) atom1658) (SparsePolynomial.merge (SparsePolynomial.scale (7496187508800 : Int) atom1659) (SparsePolynomial.scale (6223620657600 : Int) atom1660)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6958414296000 : Int) atom1661) (SparsePolynomial.scale (1828838131200 : Int) atom1662)) (SparsePolynomial.merge (SparsePolynomial.scale (2672152588800 : Int) atom1663) (SparsePolynomial.merge (SparsePolynomial.scale (28714425307200 : Int) atom1664) (SparsePolynomial.scale (31318438795200 : Int) atom1665))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20764754611200 : Int) atom1666) (SparsePolynomial.scale (47303583076800 : Int) atom1667)) (SparsePolynomial.merge (SparsePolynomial.scale (3550208205600 : Int) atom1668) (SparsePolynomial.merge (SparsePolynomial.scale (14159602504800 : Int) atom1669) (SparsePolynomial.scale (50540795877600 : Int) atom1670)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (58714949336400 : Int) atom1671) (SparsePolynomial.scale (44621368840800 : Int) atom1672)) (SparsePolynomial.merge (SparsePolynomial.scale (82584805073400 : Int) atom1673) (SparsePolynomial.merge (SparsePolynomial.scale (5924850140160 : Int) atom1674) (SparsePolynomial.scale (46603049565600 : Int) atom1675)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64561905414000 : Int) atom1676) (SparsePolynomial.scale (58431178094400 : Int) atom1677)) (SparsePolynomial.merge (SparsePolynomial.scale (83751050082600 : Int) atom1678) (SparsePolynomial.merge (SparsePolynomial.scale (38700065779200 : Int) atom1679) (SparsePolynomial.scale (81441252748800 : Int) atom1680)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (76619479413600 : Int) atom1681) (SparsePolynomial.scale (96041823897600 : Int) atom1682)) (SparsePolynomial.merge (SparsePolynomial.scale (36760668134400 : Int) atom1683) (SparsePolynomial.merge (SparsePolynomial.scale (77891482429200 : Int) atom1684) (SparsePolynomial.scale (100837655654400 : Int) atom1685))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36725564548800 : Int) atom1686) (SparsePolynomial.scale (99336377640600 : Int) atom1687)) (SparsePolynomial.merge (SparsePolynomial.scale (57215047680000 : Int) atom1688) (SparsePolynomial.merge (SparsePolynomial.scale (1735780838400 : Int) atom1689) (SparsePolynomial.scale (13628959948800 : Int) atom1690)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14833387699200 : Int) atom1691) (SparsePolynomial.scale (5586198912000 : Int) atom1692)) (SparsePolynomial.merge (SparsePolynomial.scale (20249487820800 : Int) atom1693) (SparsePolynomial.merge (SparsePolynomial.scale (906549235200 : Int) atom1694) (SparsePolynomial.scale (9616380480000 : Int) atom1695)))))))) := by decide +kernel
theorem block022_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block022 := by
  rw [block022_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1616_nonneg g hg hA hB) (atom1617_nonneg g hg hA hB)) (add_nonneg (atom1618_nonneg g hg hA hB) (add_nonneg (atom1619_nonneg g hg hA hB) (atom1620_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1621_nonneg g hg hA hB) (atom1622_nonneg g hg hA hB)) (add_nonneg (atom1623_nonneg g hg hA hB) (add_nonneg (atom1624_nonneg g hg hA hB) (atom1625_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1626_nonneg g hg hA hB) (atom1627_nonneg g hg hA hB)) (add_nonneg (atom1628_nonneg g hg hA hB) (add_nonneg (atom1629_nonneg g hg hA hB) (atom1630_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1631_nonneg g hg hA hB) (atom1632_nonneg g hg hA hB)) (add_nonneg (atom1633_nonneg g hg hA hB) (add_nonneg (atom1634_nonneg g hg hA hB) (atom1635_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1636_nonneg g hg hA hB) (atom1637_nonneg g hg hA hB)) (add_nonneg (atom1638_nonneg g hg hA hB) (add_nonneg (atom1639_nonneg g hg hA hB) (atom1640_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1641_nonneg g hg hA hB) (atom1642_nonneg g hg hA hB)) (add_nonneg (atom1643_nonneg g hg hA hB) (add_nonneg (atom1644_nonneg g hg hA hB) (atom1645_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1646_nonneg g hg hA hB) (atom1647_nonneg g hg hA hB)) (add_nonneg (atom1648_nonneg g hg hA hB) (add_nonneg (atom1649_nonneg g hg hA hB) (atom1650_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1651_nonneg g hg hA hB) (atom1652_nonneg g hg hA hB)) (add_nonneg (atom1653_nonneg g hg hA hB) (add_nonneg (atom1654_nonneg g hg hA hB) (atom1655_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1656_nonneg g hg hA hB) (atom1657_nonneg g hg hA hB)) (add_nonneg (atom1658_nonneg g hg hA hB) (add_nonneg (atom1659_nonneg g hg hA hB) (atom1660_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1661_nonneg g hg hA hB) (atom1662_nonneg g hg hA hB)) (add_nonneg (atom1663_nonneg g hg hA hB) (add_nonneg (atom1664_nonneg g hg hA hB) (atom1665_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1666_nonneg g hg hA hB) (atom1667_nonneg g hg hA hB)) (add_nonneg (atom1668_nonneg g hg hA hB) (add_nonneg (atom1669_nonneg g hg hA hB) (atom1670_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1671_nonneg g hg hA hB) (atom1672_nonneg g hg hA hB)) (add_nonneg (atom1673_nonneg g hg hA hB) (add_nonneg (atom1674_nonneg g hg hA hB) (atom1675_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1676_nonneg g hg hA hB) (atom1677_nonneg g hg hA hB)) (add_nonneg (atom1678_nonneg g hg hA hB) (add_nonneg (atom1679_nonneg g hg hA hB) (atom1680_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1681_nonneg g hg hA hB) (atom1682_nonneg g hg hA hB)) (add_nonneg (atom1683_nonneg g hg hA hB) (add_nonneg (atom1684_nonneg g hg hA hB) (atom1685_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1686_nonneg g hg hA hB) (atom1687_nonneg g hg hA hB)) (add_nonneg (atom1688_nonneg g hg hA hB) (add_nonneg (atom1689_nonneg g hg hA hB) (atom1690_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1691_nonneg g hg hA hB) (atom1692_nonneg g hg hA hB)) (add_nonneg (atom1693_nonneg g hg hA hB) (add_nonneg (atom1694_nonneg g hg hA hB) (atom1695_nonneg g hg hA hB))))))))

end APPT.Finite21
