import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1649 : SparsePolynomial.Poly := [([6,8,9], 1)]
theorem eval_atom1649 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1649 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom1649, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1649_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19897350303600 : Int) atom1649) := by
  rw [SparsePolynomial.eval_scale, eval_atom1649]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1650 : SparsePolynomial.Poly := [([6,8,13], 1)]
theorem eval_atom1650 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1650 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom1650, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1650_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5145488409600 : Int) atom1650) := by
  rw [SparsePolynomial.eval_scale, eval_atom1650]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1651 : SparsePolynomial.Poly := [([6,8,14], 1)]
theorem eval_atom1651 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1651 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom1651, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1651_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10290976819200 : Int) atom1651) := by
  rw [SparsePolynomial.eval_scale, eval_atom1651]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1652 : SparsePolynomial.Poly := [([6,8,15], 1)]
theorem eval_atom1652 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1652 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom1652, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1652_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15436465228800 : Int) atom1652) := by
  rw [SparsePolynomial.eval_scale, eval_atom1652]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1653 : SparsePolynomial.Poly := [([6,8,16], 1)]
theorem eval_atom1653 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1653 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom1653, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1653_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20581953638400 : Int) atom1653) := by
  rw [SparsePolynomial.eval_scale, eval_atom1653]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1654 : SparsePolynomial.Poly := [([6,8,17], 1)]
theorem eval_atom1654 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1654 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom1654, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1654_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25727442048000 : Int) atom1654) := by
  rw [SparsePolynomial.eval_scale, eval_atom1654]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1655 : SparsePolynomial.Poly := [([6,8,18], 1)]
theorem eval_atom1655 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1655 = ((g 6) * (g 8) * (g 18)) := by
  norm_num [atom1655, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1655_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11587980096000 : Int) atom1655) := by
  rw [SparsePolynomial.eval_scale, eval_atom1655]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1656 : SparsePolynomial.Poly := [([6,8,19], 1)]
theorem eval_atom1656 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1656 = ((g 6) * (g 8) * (g 19)) := by
  norm_num [atom1656, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1656_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19816509081600 : Int) atom1656) := by
  rw [SparsePolynomial.eval_scale, eval_atom1656]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1657 : SparsePolynomial.Poly := [([6,8,20], 1)]
theorem eval_atom1657 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1657 = ((g 6) * (g 8) * (g 20)) := by
  norm_num [atom1657, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1657_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28045038067200 : Int) atom1657) := by
  rw [SparsePolynomial.eval_scale, eval_atom1657]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1658 : SparsePolynomial.Poly := [([6,8,21], 1)]
theorem eval_atom1658 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1658 = ((g 6) * (g 8) * (g 21)) := by
  norm_num [atom1658, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1658_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101836019577600 : Int) atom1658) := by
  rw [SparsePolynomial.eval_scale, eval_atom1658]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1659 : SparsePolynomial.Poly := [([6,8,22], 1)]
theorem eval_atom1659 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1659 = ((g 6) * (g 8) * (g 22)) := by
  norm_num [atom1659, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1659_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175627001088000 : Int) atom1659) := by
  rw [SparsePolynomial.eval_scale, eval_atom1659]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1660 : SparsePolynomial.Poly := [([6,8,23], 1)]
theorem eval_atom1660 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1660 = ((g 6) * (g 8) * (g 23)) := by
  norm_num [atom1660, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1660_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (259831217923200 : Int) atom1660) := by
  rw [SparsePolynomial.eval_scale, eval_atom1660]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom1661 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1661 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1661_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31293969260400 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1662 : SparsePolynomial.Poly := [([6,9,10], 1)]
theorem eval_atom1662 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1662 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom1662, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1662_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43670515451904 : Int) atom1662) := by
  rw [SparsePolynomial.eval_scale, eval_atom1662]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1663 : SparsePolynomial.Poly := [([6,9,11], 1)]
theorem eval_atom1663 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1663 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom1663, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1663_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22669871994000 : Int) atom1663) := by
  rw [SparsePolynomial.eval_scale, eval_atom1663]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1664 : SparsePolynomial.Poly := [([6,9,12], 1)]
theorem eval_atom1664 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1664 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom1664, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1664_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26794767661200 : Int) atom1664) := by
  rw [SparsePolynomial.eval_scale, eval_atom1664]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1665 : SparsePolynomial.Poly := [([6,9,13], 1)]
theorem eval_atom1665 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1665 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom1665, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1665_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29899070586000 : Int) atom1665) := by
  rw [SparsePolynomial.eval_scale, eval_atom1665]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1666 : SparsePolynomial.Poly := [([6,9,14], 1)]
theorem eval_atom1666 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1666 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom1666, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1666_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36086414086800 : Int) atom1666) := by
  rw [SparsePolynomial.eval_scale, eval_atom1666]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1667 : SparsePolynomial.Poly := [([6,9,15], 1)]
theorem eval_atom1667 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1667 = ((g 6) * (g 9) * (g 15)) := by
  norm_num [atom1667, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1667_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42273757587600 : Int) atom1667) := by
  rw [SparsePolynomial.eval_scale, eval_atom1667]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1668 : SparsePolynomial.Poly := [([6,9,16], 1)]
theorem eval_atom1668 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1668 = ((g 6) * (g 9) * (g 16)) := by
  norm_num [atom1668, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1668_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48461101088400 : Int) atom1668) := by
  rw [SparsePolynomial.eval_scale, eval_atom1668]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1669 : SparsePolynomial.Poly := [([6,9,17], 1)]
theorem eval_atom1669 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1669 = ((g 6) * (g 9) * (g 17)) := by
  norm_num [atom1669, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1669_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54648444589200 : Int) atom1669) := by
  rw [SparsePolynomial.eval_scale, eval_atom1669]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1670 : SparsePolynomial.Poly := [([6,9,18], 1)]
theorem eval_atom1670 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1670 = ((g 6) * (g 9) * (g 18)) := by
  norm_num [atom1670, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1670_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47823313522248 : Int) atom1670) := by
  rw [SparsePolynomial.eval_scale, eval_atom1670]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1671 : SparsePolynomial.Poly := [([6,9,19], 1)]
theorem eval_atom1671 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1671 = ((g 6) * (g 9) * (g 19)) := by
  norm_num [atom1671, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1671_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65569641223680 : Int) atom1671) := by
  rw [SparsePolynomial.eval_scale, eval_atom1671]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1672 : SparsePolynomial.Poly := [([6,9,20], 1)]
theorem eval_atom1672 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1672 = ((g 6) * (g 9) * (g 20)) := by
  norm_num [atom1672, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1672_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83315968925112 : Int) atom1672) := by
  rw [SparsePolynomial.eval_scale, eval_atom1672]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1673 : SparsePolynomial.Poly := [([6,9,21], 1)]
theorem eval_atom1673 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1673 = ((g 6) * (g 9) * (g 21)) := by
  norm_num [atom1673, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1673_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (168997180831380 : Int) atom1673) := by
  rw [SparsePolynomial.eval_scale, eval_atom1673]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1674 : SparsePolynomial.Poly := [([6,9,22], 1)]
theorem eval_atom1674 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1674 = ((g 6) * (g 9) * (g 22)) := by
  norm_num [atom1674, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1674_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254678392737648 : Int) atom1674) := by
  rw [SparsePolynomial.eval_scale, eval_atom1674]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1675 : SparsePolynomial.Poly := [([6,9,23], 1)]
theorem eval_atom1675 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1675 = ((g 6) * (g 9) * (g 23)) := by
  norm_num [atom1675, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1675_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (349755587977950 : Int) atom1675) := by
  rw [SparsePolynomial.eval_scale, eval_atom1675]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1676 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom1676 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1676 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom1676, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1676_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41144504117904 : Int) atom1676) := by
  rw [SparsePolynomial.eval_scale, eval_atom1676]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1677 : SparsePolynomial.Poly := [([6,10,11], 1)]
theorem eval_atom1677 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1677 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom1677, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1677_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68517563369904 : Int) atom1677) := by
  rw [SparsePolynomial.eval_scale, eval_atom1677]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1678 : SparsePolynomial.Poly := [([6,10,12], 1)]
theorem eval_atom1678 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1678 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom1678, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1678_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69580680809904 : Int) atom1678) := by
  rw [SparsePolynomial.eval_scale, eval_atom1678]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1679 : SparsePolynomial.Poly := [([6,10,13], 1)]
theorem eval_atom1679 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1679 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom1679, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1679_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75789286659504 : Int) atom1679) := by
  rw [SparsePolynomial.eval_scale, eval_atom1679]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1680 : SparsePolynomial.Poly := [([6,10,14], 1)]
theorem eval_atom1680 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1680 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom1680, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1680_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81997892509104 : Int) atom1680) := by
  rw [SparsePolynomial.eval_scale, eval_atom1680]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1681 : SparsePolynomial.Poly := [([6,10,15], 1)]
theorem eval_atom1681 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1681 = ((g 6) * (g 10) * (g 15)) := by
  norm_num [atom1681, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1681_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88206498358704 : Int) atom1681) := by
  rw [SparsePolynomial.eval_scale, eval_atom1681]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1682 : SparsePolynomial.Poly := [([6,10,16], 1)]
theorem eval_atom1682 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1682 = ((g 6) * (g 10) * (g 16)) := by
  norm_num [atom1682, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1682_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (94415104208304 : Int) atom1682) := by
  rw [SparsePolynomial.eval_scale, eval_atom1682]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1683 : SparsePolynomial.Poly := [([6,10,17], 1)]
theorem eval_atom1683 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1683 = ((g 6) * (g 10) * (g 17)) := by
  norm_num [atom1683, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1683_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100623710057904 : Int) atom1683) := by
  rw [SparsePolynomial.eval_scale, eval_atom1683]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1684 : SparsePolynomial.Poly := [([6,10,18], 1)]
theorem eval_atom1684 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1684 = ((g 6) * (g 10) * (g 18)) := by
  norm_num [atom1684, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1684_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99978636340440 : Int) atom1684) := by
  rw [SparsePolynomial.eval_scale, eval_atom1684]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1685 : SparsePolynomial.Poly := [([6,10,19], 1)]
theorem eval_atom1685 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1685 = ((g 6) * (g 10) * (g 19)) := by
  norm_num [atom1685, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1685_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (122637785402880 : Int) atom1685) := by
  rw [SparsePolynomial.eval_scale, eval_atom1685]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1686 : SparsePolynomial.Poly := [([6,10,20], 1)]
theorem eval_atom1686 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1686 = ((g 6) * (g 10) * (g 20)) := by
  norm_num [atom1686, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1686_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145296934465320 : Int) atom1686) := by
  rw [SparsePolynomial.eval_scale, eval_atom1686]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1687 : SparsePolynomial.Poly := [([6,10,21], 1)]
theorem eval_atom1687 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1687 = ((g 6) * (g 10) * (g 21)) := by
  norm_num [atom1687, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1687_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229643480261052 : Int) atom1687) := by
  rw [SparsePolynomial.eval_scale, eval_atom1687]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1688 : SparsePolynomial.Poly := [([6,10,22], 1)]
theorem eval_atom1688 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1688 = ((g 6) * (g 10) * (g 22)) := by
  norm_num [atom1688, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1688_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (313990026056784 : Int) atom1688) := by
  rw [SparsePolynomial.eval_scale, eval_atom1688]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1689 : SparsePolynomial.Poly := [([6,10,23], 1)]
theorem eval_atom1689 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1689 = ((g 6) * (g 10) * (g 23)) := by
  norm_num [atom1689, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1689_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (405876047439258 : Int) atom1689) := by
  rw [SparsePolynomial.eval_scale, eval_atom1689]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom1690 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1690 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1690_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62307098330400 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1691 : SparsePolynomial.Poly := [([6,11,12], 1)]
theorem eval_atom1691 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1691 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom1691, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1691_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104900012632800 : Int) atom1691) := by
  rw [SparsePolynomial.eval_scale, eval_atom1691]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1692 : SparsePolynomial.Poly := [([6,11,13], 1)]
theorem eval_atom1692 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1692 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom1692, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1692_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (107026247512800 : Int) atom1692) := by
  rw [SparsePolynomial.eval_scale, eval_atom1692]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1693 : SparsePolynomial.Poly := [([6,11,14], 1)]
theorem eval_atom1693 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1693 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom1693, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1693_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109152482392800 : Int) atom1693) := by
  rw [SparsePolynomial.eval_scale, eval_atom1693]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1694 : SparsePolynomial.Poly := [([6,11,15], 1)]
theorem eval_atom1694 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1694 = ((g 6) * (g 11) * (g 15)) := by
  norm_num [atom1694, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1694_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (111278717272800 : Int) atom1694) := by
  rw [SparsePolynomial.eval_scale, eval_atom1694]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1695 : SparsePolynomial.Poly := [([6,11,16], 1)]
theorem eval_atom1695 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1695 = ((g 6) * (g 11) * (g 16)) := by
  norm_num [atom1695, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1695_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116487992728800 : Int) atom1695) := by
  rw [SparsePolynomial.eval_scale, eval_atom1695]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1696 : SparsePolynomial.Poly := [([6,11,17], 1)]
theorem eval_atom1696 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1696 = ((g 6) * (g 11) * (g 17)) := by
  norm_num [atom1696, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1696_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121697268184800 : Int) atom1696) := by
  rw [SparsePolynomial.eval_scale, eval_atom1696]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1697 : SparsePolynomial.Poly := [([6,11,18], 1)]
theorem eval_atom1697 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1697 = ((g 6) * (g 11) * (g 18)) := by
  norm_num [atom1697, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1697_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (142977134375856 : Int) atom1697) := by
  rw [SparsePolynomial.eval_scale, eval_atom1697]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1698 : SparsePolynomial.Poly := [([6,11,19], 1)]
theorem eval_atom1698 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1698 = ((g 6) * (g 11) * (g 19)) := by
  norm_num [atom1698, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1698_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164808313021440 : Int) atom1698) := by
  rw [SparsePolynomial.eval_scale, eval_atom1698]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1699 : SparsePolynomial.Poly := [([6,11,20], 1)]
theorem eval_atom1699 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1699 = ((g 6) * (g 11) * (g 20)) := by
  norm_num [atom1699, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1699_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (208556285438160 : Int) atom1699) := by
  rw [SparsePolynomial.eval_scale, eval_atom1699]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1700 : SparsePolynomial.Poly := [([6,11,21], 1)]
theorem eval_atom1700 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1700 = ((g 6) * (g 11) * (g 21)) := by
  norm_num [atom1700, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1700_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (289029266970840 : Int) atom1700) := by
  rw [SparsePolynomial.eval_scale, eval_atom1700]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1701 : SparsePolynomial.Poly := [([6,11,22], 1)]
theorem eval_atom1701 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1701 = ((g 6) * (g 11) * (g 22)) := by
  norm_num [atom1701, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1701_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (379790294156064 : Int) atom1701) := by
  rw [SparsePolynomial.eval_scale, eval_atom1701]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1702 : SparsePolynomial.Poly := [([6,11,23], 1)]
theorem eval_atom1702 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1702 = ((g 6) * (g 11) * (g 23)) := by
  norm_num [atom1702, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1702_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (475393062860100 : Int) atom1702) := by
  rw [SparsePolynomial.eval_scale, eval_atom1702]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1703 : SparsePolynomial.Poly := [([6,12,12], 1)]
theorem eval_atom1703 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1703 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom1703, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1703_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77526953380800 : Int) atom1703) := by
  rw [SparsePolynomial.eval_scale, eval_atom1703]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1704 : SparsePolynomial.Poly := [([6,12,13], 1)]
theorem eval_atom1704 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1704 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom1704, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1704_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146429366529600 : Int) atom1704) := by
  rw [SparsePolynomial.eval_scale, eval_atom1704]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1705 : SparsePolynomial.Poly := [([6,12,14], 1)]
theorem eval_atom1705 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1705 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom1705, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1705_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149618718849600 : Int) atom1705) := by
  rw [SparsePolynomial.eval_scale, eval_atom1705]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1706 : SparsePolynomial.Poly := [([6,12,15], 1)]
theorem eval_atom1706 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1706 = ((g 6) * (g 12) * (g 15)) := by
  norm_num [atom1706, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1706_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152808071169600 : Int) atom1706) := by
  rw [SparsePolynomial.eval_scale, eval_atom1706]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1707 : SparsePolynomial.Poly := [([6,12,16], 1)]
theorem eval_atom1707 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1707 = ((g 6) * (g 12) * (g 16)) := by
  norm_num [atom1707, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1707_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (155997423489600 : Int) atom1707) := by
  rw [SparsePolynomial.eval_scale, eval_atom1707]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1708 : SparsePolynomial.Poly := [([6,12,17], 1)]
theorem eval_atom1708 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1708 = ((g 6) * (g 12) * (g 17)) := by
  norm_num [atom1708, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1708_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159186775809600 : Int) atom1708) := by
  rw [SparsePolynomial.eval_scale, eval_atom1708]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1709 : SparsePolynomial.Poly := [([6,12,18], 1)]
theorem eval_atom1709 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1709 = ((g 6) * (g 12) * (g 18)) := by
  norm_num [atom1709, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1709_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (219028702232736 : Int) atom1709) := by
  rw [SparsePolynomial.eval_scale, eval_atom1709]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1710 : SparsePolynomial.Poly := [([6,12,19], 1)]
theorem eval_atom1710 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1710 = ((g 6) * (g 12) * (g 19)) := by
  norm_num [atom1710, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1710_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (218857203671040 : Int) atom1710) := by
  rw [SparsePolynomial.eval_scale, eval_atom1710]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1711 : SparsePolynomial.Poly := [([6,12,20], 1)]
theorem eval_atom1711 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1711 = ((g 6) * (g 12) * (g 20)) := by
  norm_num [atom1711, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1711_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (328731745304160 : Int) atom1711) := by
  rw [SparsePolynomial.eval_scale, eval_atom1711]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1712 : SparsePolynomial.Poly := [([6,12,21], 1)]
theorem eval_atom1712 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1712 = ((g 6) * (g 12) * (g 21)) := by
  norm_num [atom1712, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1712_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (342942277922640 : Int) atom1712) := by
  rw [SparsePolynomial.eval_scale, eval_atom1712]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1713 : SparsePolynomial.Poly := [([6,12,22], 1)]
theorem eval_atom1713 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1713 = ((g 6) * (g 12) * (g 22)) := by
  norm_num [atom1713, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1713_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (426827127950784 : Int) atom1713) := by
  rw [SparsePolynomial.eval_scale, eval_atom1713]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1714 : SparsePolynomial.Poly := [([6,12,23], 1)]
theorem eval_atom1714 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1714 = ((g 6) * (g 12) * (g 23)) := by
  norm_num [atom1714, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1714_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (511824270295800 : Int) atom1714) := by
  rw [SparsePolynomial.eval_scale, eval_atom1714]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1715 : SparsePolynomial.Poly := [([6,13,13], 1)]
theorem eval_atom1715 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1715 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom1715, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1715_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103836452227200 : Int) atom1715) := by
  rw [SparsePolynomial.eval_scale, eval_atom1715]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1716 : SparsePolynomial.Poly := [([6,13,14], 1)]
theorem eval_atom1716 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1716 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom1716, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1716_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (195494894179200 : Int) atom1716) := by
  rw [SparsePolynomial.eval_scale, eval_atom1716]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1717 : SparsePolynomial.Poly := [([6,13,15], 1)]
theorem eval_atom1717 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1717 = ((g 6) * (g 13) * (g 15)) := by
  norm_num [atom1717, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1717_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (192560690044800 : Int) atom1717) := by
  rw [SparsePolynomial.eval_scale, eval_atom1717]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1718 : SparsePolynomial.Poly := [([6,13,16], 1)]
theorem eval_atom1718 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1718 = ((g 6) * (g 13) * (g 16)) := by
  norm_num [atom1718, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1718_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (192709526486400 : Int) atom1718) := by
  rw [SparsePolynomial.eval_scale, eval_atom1718]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1719 : SparsePolynomial.Poly := [([6,13,17], 1)]
theorem eval_atom1719 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1719 = ((g 6) * (g 13) * (g 17)) := by
  norm_num [atom1719, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1719_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (192858362928000 : Int) atom1719) := by
  rw [SparsePolynomial.eval_scale, eval_atom1719]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1720 : SparsePolynomial.Poly := [([6,13,18], 1)]
theorem eval_atom1720 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1720 = ((g 6) * (g 13) * (g 18)) := by
  norm_num [atom1720, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1720_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241236824875200 : Int) atom1720) := by
  rw [SparsePolynomial.eval_scale, eval_atom1720]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1721 : SparsePolynomial.Poly := [([6,13,19], 1)]
theorem eval_atom1721 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1721 = ((g 6) * (g 13) * (g 19)) := by
  norm_num [atom1721, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1721_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (242826237561600 : Int) atom1721) := by
  rw [SparsePolynomial.eval_scale, eval_atom1721]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1722 : SparsePolynomial.Poly := [([6,13,20], 1)]
theorem eval_atom1722 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1722 = ((g 6) * (g 13) * (g 20)) := by
  norm_num [atom1722, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1722_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (356418199368000 : Int) atom1722) := by
  rw [SparsePolynomial.eval_scale, eval_atom1722]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1723 : SparsePolynomial.Poly := [([6,13,21], 1)]
theorem eval_atom1723 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1723 = ((g 6) * (g 13) * (g 21)) := by
  norm_num [atom1723, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1723_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (364599695829600 : Int) atom1723) := by
  rw [SparsePolynomial.eval_scale, eval_atom1723]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1724 : SparsePolynomial.Poly := [([6,13,22], 1)]
theorem eval_atom1724 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1724 = ((g 6) * (g 13) * (g 22)) := by
  norm_num [atom1724, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1724_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (450159465571200 : Int) atom1724) := by
  rw [SparsePolynomial.eval_scale, eval_atom1724]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1725 : SparsePolynomial.Poly := [([6,13,23], 1)]
theorem eval_atom1725 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1725 = ((g 6) * (g 13) * (g 23)) := by
  norm_num [atom1725, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1725_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (537932773501200 : Int) atom1725) := by
  rw [SparsePolynomial.eval_scale, eval_atom1725]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1726 : SparsePolynomial.Poly := [([6,14,14], 1)]
theorem eval_atom1726 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1726 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom1726, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1726_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126592481030400 : Int) atom1726) := by
  rw [SparsePolynomial.eval_scale, eval_atom1726]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1727 : SparsePolynomial.Poly := [([6,14,15], 1)]
theorem eval_atom1727 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1727 = ((g 6) * (g 14) * (g 15)) := by
  norm_num [atom1727, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1727_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241054792070400 : Int) atom1727) := by
  rw [SparsePolynomial.eval_scale, eval_atom1727]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1728 : SparsePolynomial.Poly := [([6,14,16], 1)]
theorem eval_atom1728 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1728 = ((g 6) * (g 14) * (g 16)) := by
  norm_num [atom1728, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1728_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (237142519891200 : Int) atom1728) := by
  rw [SparsePolynomial.eval_scale, eval_atom1728]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block023 : SparsePolynomial.Poly := [([6,8,9], 19897350303600), ([6,8,13], 5145488409600), ([6,8,14], 10290976819200), ([6,8,15], 15436465228800), ([6,8,16], 20581953638400), ([6,8,17], 25727442048000), ([6,8,18], 11587980096000), ([6,8,19], 19816509081600), ([6,8,20], 28045038067200), ([6,8,21], 101836019577600), ([6,8,22], 175627001088000), ([6,8,23], 259831217923200), ([6,9,9], 31293969260400), ([6,9,10], 43670515451904), ([6,9,11], 22669871994000), ([6,9,12], 26794767661200), ([6,9,13], 29899070586000), ([6,9,14], 36086414086800), ([6,9,15], 42273757587600), ([6,9,16], 48461101088400), ([6,9,17], 54648444589200), ([6,9,18], 47823313522248), ([6,9,19], 65569641223680), ([6,9,20], 83315968925112), ([6,9,21], 168997180831380), ([6,9,22], 254678392737648), ([6,9,23], 349755587977950), ([6,10,10], 41144504117904), ([6,10,11], 68517563369904), ([6,10,12], 69580680809904), ([6,10,13], 75789286659504), ([6,10,14], 81997892509104), ([6,10,15], 88206498358704), ([6,10,16], 94415104208304), ([6,10,17], 100623710057904), ([6,10,18], 99978636340440), ([6,10,19], 122637785402880), ([6,10,20], 145296934465320), ([6,10,21], 229643480261052), ([6,10,22], 313990026056784), ([6,10,23], 405876047439258), ([6,11,11], 62307098330400), ([6,11,12], 104900012632800), ([6,11,13], 107026247512800), ([6,11,14], 109152482392800), ([6,11,15], 111278717272800), ([6,11,16], 116487992728800), ([6,11,17], 121697268184800), ([6,11,18], 142977134375856), ([6,11,19], 164808313021440), ([6,11,20], 208556285438160), ([6,11,21], 289029266970840), ([6,11,22], 379790294156064), ([6,11,23], 475393062860100), ([6,12,12], 77526953380800), ([6,12,13], 146429366529600), ([6,12,14], 149618718849600), ([6,12,15], 152808071169600), ([6,12,16], 155997423489600), ([6,12,17], 159186775809600), ([6,12,18], 219028702232736), ([6,12,19], 218857203671040), ([6,12,20], 328731745304160), ([6,12,21], 342942277922640), ([6,12,22], 426827127950784), ([6,12,23], 511824270295800), ([6,13,13], 103836452227200), ([6,13,14], 195494894179200), ([6,13,15], 192560690044800), ([6,13,16], 192709526486400), ([6,13,17], 192858362928000), ([6,13,18], 241236824875200), ([6,13,19], 242826237561600), ([6,13,20], 356418199368000), ([6,13,21], 364599695829600), ([6,13,22], 450159465571200), ([6,13,23], 537932773501200), ([6,14,14], 126592481030400), ([6,14,15], 241054792070400), ([6,14,16], 237142519891200)]
theorem block023_data : block023 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19897350303600 : Int) atom1649) (SparsePolynomial.scale (5145488409600 : Int) atom1650)) (SparsePolynomial.merge (SparsePolynomial.scale (10290976819200 : Int) atom1651) (SparsePolynomial.merge (SparsePolynomial.scale (15436465228800 : Int) atom1652) (SparsePolynomial.scale (20581953638400 : Int) atom1653)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25727442048000 : Int) atom1654) (SparsePolynomial.scale (11587980096000 : Int) atom1655)) (SparsePolynomial.merge (SparsePolynomial.scale (19816509081600 : Int) atom1656) (SparsePolynomial.merge (SparsePolynomial.scale (28045038067200 : Int) atom1657) (SparsePolynomial.scale (101836019577600 : Int) atom1658))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (175627001088000 : Int) atom1659) (SparsePolynomial.scale (259831217923200 : Int) atom1660)) (SparsePolynomial.merge (SparsePolynomial.scale (31293969260400 : Int) atom1661) (SparsePolynomial.merge (SparsePolynomial.scale (43670515451904 : Int) atom1662) (SparsePolynomial.scale (22669871994000 : Int) atom1663)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26794767661200 : Int) atom1664) (SparsePolynomial.scale (29899070586000 : Int) atom1665)) (SparsePolynomial.merge (SparsePolynomial.scale (36086414086800 : Int) atom1666) (SparsePolynomial.merge (SparsePolynomial.scale (42273757587600 : Int) atom1667) (SparsePolynomial.scale (48461101088400 : Int) atom1668)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (54648444589200 : Int) atom1669) (SparsePolynomial.scale (47823313522248 : Int) atom1670)) (SparsePolynomial.merge (SparsePolynomial.scale (65569641223680 : Int) atom1671) (SparsePolynomial.merge (SparsePolynomial.scale (83315968925112 : Int) atom1672) (SparsePolynomial.scale (168997180831380 : Int) atom1673)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (254678392737648 : Int) atom1674) (SparsePolynomial.scale (349755587977950 : Int) atom1675)) (SparsePolynomial.merge (SparsePolynomial.scale (41144504117904 : Int) atom1676) (SparsePolynomial.merge (SparsePolynomial.scale (68517563369904 : Int) atom1677) (SparsePolynomial.scale (69580680809904 : Int) atom1678))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (75789286659504 : Int) atom1679) (SparsePolynomial.scale (81997892509104 : Int) atom1680)) (SparsePolynomial.merge (SparsePolynomial.scale (88206498358704 : Int) atom1681) (SparsePolynomial.merge (SparsePolynomial.scale (94415104208304 : Int) atom1682) (SparsePolynomial.scale (100623710057904 : Int) atom1683)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (99978636340440 : Int) atom1684) (SparsePolynomial.scale (122637785402880 : Int) atom1685)) (SparsePolynomial.merge (SparsePolynomial.scale (145296934465320 : Int) atom1686) (SparsePolynomial.merge (SparsePolynomial.scale (229643480261052 : Int) atom1687) (SparsePolynomial.scale (313990026056784 : Int) atom1688))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (405876047439258 : Int) atom1689) (SparsePolynomial.scale (62307098330400 : Int) atom1690)) (SparsePolynomial.merge (SparsePolynomial.scale (104900012632800 : Int) atom1691) (SparsePolynomial.merge (SparsePolynomial.scale (107026247512800 : Int) atom1692) (SparsePolynomial.scale (109152482392800 : Int) atom1693)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (111278717272800 : Int) atom1694) (SparsePolynomial.scale (116487992728800 : Int) atom1695)) (SparsePolynomial.merge (SparsePolynomial.scale (121697268184800 : Int) atom1696) (SparsePolynomial.merge (SparsePolynomial.scale (142977134375856 : Int) atom1697) (SparsePolynomial.scale (164808313021440 : Int) atom1698))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (208556285438160 : Int) atom1699) (SparsePolynomial.scale (289029266970840 : Int) atom1700)) (SparsePolynomial.merge (SparsePolynomial.scale (379790294156064 : Int) atom1701) (SparsePolynomial.merge (SparsePolynomial.scale (475393062860100 : Int) atom1702) (SparsePolynomial.scale (77526953380800 : Int) atom1703)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (146429366529600 : Int) atom1704) (SparsePolynomial.scale (149618718849600 : Int) atom1705)) (SparsePolynomial.merge (SparsePolynomial.scale (152808071169600 : Int) atom1706) (SparsePolynomial.merge (SparsePolynomial.scale (155997423489600 : Int) atom1707) (SparsePolynomial.scale (159186775809600 : Int) atom1708)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (219028702232736 : Int) atom1709) (SparsePolynomial.scale (218857203671040 : Int) atom1710)) (SparsePolynomial.merge (SparsePolynomial.scale (328731745304160 : Int) atom1711) (SparsePolynomial.merge (SparsePolynomial.scale (342942277922640 : Int) atom1712) (SparsePolynomial.scale (426827127950784 : Int) atom1713)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (511824270295800 : Int) atom1714) (SparsePolynomial.scale (103836452227200 : Int) atom1715)) (SparsePolynomial.merge (SparsePolynomial.scale (195494894179200 : Int) atom1716) (SparsePolynomial.merge (SparsePolynomial.scale (192560690044800 : Int) atom1717) (SparsePolynomial.scale (192709526486400 : Int) atom1718))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (192858362928000 : Int) atom1719) (SparsePolynomial.scale (241236824875200 : Int) atom1720)) (SparsePolynomial.merge (SparsePolynomial.scale (242826237561600 : Int) atom1721) (SparsePolynomial.merge (SparsePolynomial.scale (356418199368000 : Int) atom1722) (SparsePolynomial.scale (364599695829600 : Int) atom1723)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (450159465571200 : Int) atom1724) (SparsePolynomial.scale (537932773501200 : Int) atom1725)) (SparsePolynomial.merge (SparsePolynomial.scale (126592481030400 : Int) atom1726) (SparsePolynomial.merge (SparsePolynomial.scale (241054792070400 : Int) atom1727) (SparsePolynomial.scale (237142519891200 : Int) atom1728)))))))) := by decide +kernel
theorem block023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block023 := by
  rw [block023_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1649_nonneg g hg hA hB) (atom1650_nonneg g hg hA hB)) (add_nonneg (atom1651_nonneg g hg hA hB) (add_nonneg (atom1652_nonneg g hg hA hB) (atom1653_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1654_nonneg g hg hA hB) (atom1655_nonneg g hg hA hB)) (add_nonneg (atom1656_nonneg g hg hA hB) (add_nonneg (atom1657_nonneg g hg hA hB) (atom1658_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1659_nonneg g hg hA hB) (atom1660_nonneg g hg hA hB)) (add_nonneg (atom1661_nonneg g hg hA hB) (add_nonneg (atom1662_nonneg g hg hA hB) (atom1663_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1664_nonneg g hg hA hB) (atom1665_nonneg g hg hA hB)) (add_nonneg (atom1666_nonneg g hg hA hB) (add_nonneg (atom1667_nonneg g hg hA hB) (atom1668_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1669_nonneg g hg hA hB) (atom1670_nonneg g hg hA hB)) (add_nonneg (atom1671_nonneg g hg hA hB) (add_nonneg (atom1672_nonneg g hg hA hB) (atom1673_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1674_nonneg g hg hA hB) (atom1675_nonneg g hg hA hB)) (add_nonneg (atom1676_nonneg g hg hA hB) (add_nonneg (atom1677_nonneg g hg hA hB) (atom1678_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1679_nonneg g hg hA hB) (atom1680_nonneg g hg hA hB)) (add_nonneg (atom1681_nonneg g hg hA hB) (add_nonneg (atom1682_nonneg g hg hA hB) (atom1683_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1684_nonneg g hg hA hB) (atom1685_nonneg g hg hA hB)) (add_nonneg (atom1686_nonneg g hg hA hB) (add_nonneg (atom1687_nonneg g hg hA hB) (atom1688_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1689_nonneg g hg hA hB) (atom1690_nonneg g hg hA hB)) (add_nonneg (atom1691_nonneg g hg hA hB) (add_nonneg (atom1692_nonneg g hg hA hB) (atom1693_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1694_nonneg g hg hA hB) (atom1695_nonneg g hg hA hB)) (add_nonneg (atom1696_nonneg g hg hA hB) (add_nonneg (atom1697_nonneg g hg hA hB) (atom1698_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1699_nonneg g hg hA hB) (atom1700_nonneg g hg hA hB)) (add_nonneg (atom1701_nonneg g hg hA hB) (add_nonneg (atom1702_nonneg g hg hA hB) (atom1703_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1704_nonneg g hg hA hB) (atom1705_nonneg g hg hA hB)) (add_nonneg (atom1706_nonneg g hg hA hB) (add_nonneg (atom1707_nonneg g hg hA hB) (atom1708_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1709_nonneg g hg hA hB) (atom1710_nonneg g hg hA hB)) (add_nonneg (atom1711_nonneg g hg hA hB) (add_nonneg (atom1712_nonneg g hg hA hB) (atom1713_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1714_nonneg g hg hA hB) (atom1715_nonneg g hg hA hB)) (add_nonneg (atom1716_nonneg g hg hA hB) (add_nonneg (atom1717_nonneg g hg hA hB) (atom1718_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1719_nonneg g hg hA hB) (atom1720_nonneg g hg hA hB)) (add_nonneg (atom1721_nonneg g hg hA hB) (add_nonneg (atom1722_nonneg g hg hA hB) (atom1723_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1724_nonneg g hg hA hB) (atom1725_nonneg g hg hA hB)) (add_nonneg (atom1726_nonneg g hg hA hB) (add_nonneg (atom1727_nonneg g hg hA hB) (atom1728_nonneg g hg hA hB))))))))

end APPT.Finite24
