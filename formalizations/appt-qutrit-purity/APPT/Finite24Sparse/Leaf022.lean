import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1569 : SparsePolynomial.Poly := [([5,13,16], 1)]
theorem eval_atom1569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1569 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom1569, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (245154757478400 : Int) atom1569) := by
  rw [SparsePolynomial.eval_scale, eval_atom1569]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1570 : SparsePolynomial.Poly := [([5,13,17], 1)]
theorem eval_atom1570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1570 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom1570, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241242485299200 : Int) atom1570) := by
  rw [SparsePolynomial.eval_scale, eval_atom1570]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1571 : SparsePolynomial.Poly := [([5,13,18], 1)]
theorem eval_atom1571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1571 = ((g 5) * (g 13) * (g 18)) := by
  norm_num [atom1571, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (297199359072000 : Int) atom1571) := by
  rw [SparsePolynomial.eval_scale, eval_atom1571]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1572 : SparsePolynomial.Poly := [([5,13,19], 1)]
theorem eval_atom1572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1572 = ((g 5) * (g 13) * (g 19)) := by
  norm_num [atom1572, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (289024345209600 : Int) atom1572) := by
  rw [SparsePolynomial.eval_scale, eval_atom1572]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1573 : SparsePolynomial.Poly := [([5,13,20], 1)]
theorem eval_atom1573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1573 = ((g 5) * (g 13) * (g 20)) := by
  norm_num [atom1573, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (399561282489600 : Int) atom1573) := by
  rw [SparsePolynomial.eval_scale, eval_atom1573]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1574 : SparsePolynomial.Poly := [([5,13,21], 1)]
theorem eval_atom1574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1574 = ((g 5) * (g 13) * (g 21)) := by
  norm_num [atom1574, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (392412609388800 : Int) atom1574) := by
  rw [SparsePolynomial.eval_scale, eval_atom1574]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1575 : SparsePolynomial.Poly := [([5,13,22], 1)]
theorem eval_atom1575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1575 = ((g 5) * (g 13) * (g 22)) := by
  norm_num [atom1575, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (462642209568000 : Int) atom1575) := by
  rw [SparsePolynomial.eval_scale, eval_atom1575]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1576 : SparsePolynomial.Poly := [([5,13,23], 1)]
theorem eval_atom1576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1576 = ((g 5) * (g 13) * (g 23)) := by
  norm_num [atom1576, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (532871809747200 : Int) atom1576) := by
  rw [SparsePolynomial.eval_scale, eval_atom1576]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1577 : SparsePolynomial.Poly := [([5,14,14], 1)]
theorem eval_atom1577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1577 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom1577, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150166318579200 : Int) atom1577) := by
  rw [SparsePolynomial.eval_scale, eval_atom1577]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1578 : SparsePolynomial.Poly := [([5,14,15], 1)]
theorem eval_atom1578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1578 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom1578, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (283120765804800 : Int) atom1578) := by
  rw [SparsePolynomial.eval_scale, eval_atom1578]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1579 : SparsePolynomial.Poly := [([5,14,16], 1)]
theorem eval_atom1579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1579 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom1579, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (274126792262400 : Int) atom1579) := by
  rw [SparsePolynomial.eval_scale, eval_atom1579]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1580 : SparsePolynomial.Poly := [([5,14,17], 1)]
theorem eval_atom1580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1580 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom1580, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (265132818720000 : Int) atom1580) := by
  rw [SparsePolynomial.eval_scale, eval_atom1580]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1581 : SparsePolynomial.Poly := [([5,14,18], 1)]
theorem eval_atom1581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1581 = ((g 5) * (g 14) * (g 18)) := by
  norm_num [atom1581, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (302636058278400 : Int) atom1581) := by
  rw [SparsePolynomial.eval_scale, eval_atom1581]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1582 : SparsePolynomial.Poly := [([5,14,19], 1)]
theorem eval_atom1582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1582 = ((g 5) * (g 14) * (g 19)) := by
  norm_num [atom1582, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (305305962746400 : Int) atom1582) := by
  rw [SparsePolynomial.eval_scale, eval_atom1582]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1583 : SparsePolynomial.Poly := [([5,14,20], 1)]
theorem eval_atom1583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1583 = ((g 5) * (g 14) * (g 20)) := by
  norm_num [atom1583, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (417245094604800 : Int) atom1583) := by
  rw [SparsePolynomial.eval_scale, eval_atom1583]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1584 : SparsePolynomial.Poly := [([5,14,21], 1)]
theorem eval_atom1584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1584 = ((g 5) * (g 14) * (g 21)) := by
  norm_num [atom1584, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (416219977958400 : Int) atom1584) := by
  rw [SparsePolynomial.eval_scale, eval_atom1584]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1585 : SparsePolynomial.Poly := [([5,14,22], 1)]
theorem eval_atom1585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1585 = ((g 5) * (g 14) * (g 22)) := by
  norm_num [atom1585, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (472194345823200 : Int) atom1585) := by
  rw [SparsePolynomial.eval_scale, eval_atom1585]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1586 : SparsePolynomial.Poly := [([5,14,23], 1)]
theorem eval_atom1586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1586 = ((g 5) * (g 14) * (g 23)) := by
  norm_num [atom1586, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (540748493762400 : Int) atom1586) := by
  rw [SparsePolynomial.eval_scale, eval_atom1586]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1587 : SparsePolynomial.Poly := [([5,15,15], 1)]
theorem eval_atom1587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1587 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom1587, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (174054567456000 : Int) atom1587) := by
  rw [SparsePolynomial.eval_scale, eval_atom1587]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1588 : SparsePolynomial.Poly := [([5,15,16], 1)]
theorem eval_atom1588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1588 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom1588, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (319660112217600 : Int) atom1588) := by
  rw [SparsePolynomial.eval_scale, eval_atom1588]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1589 : SparsePolynomial.Poly := [([5,15,17], 1)]
theorem eval_atom1589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1589 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom1589, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (304563844569600 : Int) atom1589) := by
  rw [SparsePolynomial.eval_scale, eval_atom1589]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1590 : SparsePolynomial.Poly := [([5,15,18], 1)]
theorem eval_atom1590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1590 = ((g 5) * (g 15) * (g 18)) := by
  norm_num [atom1590, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (338015640211200 : Int) atom1590) := by
  rw [SparsePolynomial.eval_scale, eval_atom1590]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1591 : SparsePolynomial.Poly := [([5,15,19], 1)]
theorem eval_atom1591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1591 = ((g 5) * (g 15) * (g 19)) := by
  norm_num [atom1591, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (327299245056000 : Int) atom1591) := by
  rw [SparsePolynomial.eval_scale, eval_atom1591]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1592 : SparsePolynomial.Poly := [([5,15,20], 1)]
theorem eval_atom1592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1592 = ((g 5) * (g 15) * (g 20)) := by
  norm_num [atom1592, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (464134050374400 : Int) atom1592) := by
  rw [SparsePolynomial.eval_scale, eval_atom1592]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1593 : SparsePolynomial.Poly := [([5,15,21], 1)]
theorem eval_atom1593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1593 = ((g 5) * (g 15) * (g 21)) := by
  norm_num [atom1593, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (469048055414400 : Int) atom1593) := by
  rw [SparsePolynomial.eval_scale, eval_atom1593]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1594 : SparsePolynomial.Poly := [([5,15,22], 1)]
theorem eval_atom1594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1594 = ((g 5) * (g 15) * (g 22)) := by
  norm_num [atom1594, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (460158285888000 : Int) atom1594) := by
  rw [SparsePolynomial.eval_scale, eval_atom1594]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1595 : SparsePolynomial.Poly := [([5,15,23], 1)]
theorem eval_atom1595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1595 = ((g 5) * (g 15) * (g 23)) := by
  norm_num [atom1595, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (521735242392000 : Int) atom1595) := by
  rw [SparsePolynomial.eval_scale, eval_atom1595]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1596 : SparsePolynomial.Poly := [([5,16,16], 1)]
theorem eval_atom1596 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1596 = ((g 5) * (g 16) * (g 16)) := by
  norm_num [atom1596, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1596_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189788705568000 : Int) atom1596) := by
  rw [SparsePolynomial.eval_scale, eval_atom1596]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1597 : SparsePolynomial.Poly := [([5,16,17], 1)]
theorem eval_atom1597 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1597 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom1597, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1597_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (354275216064000 : Int) atom1597) := by
  rw [SparsePolynomial.eval_scale, eval_atom1597]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1598 : SparsePolynomial.Poly := [([5,16,18], 1)]
theorem eval_atom1598 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1598 = ((g 5) * (g 16) * (g 18)) := by
  norm_num [atom1598, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1598_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (355661456774400 : Int) atom1598) := by
  rw [SparsePolynomial.eval_scale, eval_atom1598]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1599 : SparsePolynomial.Poly := [([5,16,19], 1)]
theorem eval_atom1599 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1599 = ((g 5) * (g 16) * (g 19)) := by
  norm_num [atom1599, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1599_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (344788493414400 : Int) atom1599) := by
  rw [SparsePolynomial.eval_scale, eval_atom1599]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1600 : SparsePolynomial.Poly := [([5,16,20], 1)]
theorem eval_atom1600 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1600 = ((g 5) * (g 16) * (g 20)) := by
  norm_num [atom1600, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1600_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (481466730528000 : Int) atom1600) := by
  rw [SparsePolynomial.eval_scale, eval_atom1600]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1601 : SparsePolynomial.Poly := [([5,16,21], 1)]
theorem eval_atom1601 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1601 = ((g 5) * (g 16) * (g 21)) := by
  norm_num [atom1601, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1601_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (489364229692800 : Int) atom1601) := by
  rw [SparsePolynomial.eval_scale, eval_atom1601]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1602 : SparsePolynomial.Poly := [([5,16,22], 1)]
theorem eval_atom1602 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1602 = ((g 5) * (g 16) * (g 22)) := by
  norm_num [atom1602, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1602_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (425664957312000 : Int) atom1602) := by
  rw [SparsePolynomial.eval_scale, eval_atom1602]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1603 : SparsePolynomial.Poly := [([5,16,23], 1)]
theorem eval_atom1603 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1603 = ((g 5) * (g 16) * (g 23)) := by
  norm_num [atom1603, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1603_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (568330230081600 : Int) atom1603) := by
  rw [SparsePolynomial.eval_scale, eval_atom1603]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1604 : SparsePolynomial.Poly := [([5,17,17], 1)]
theorem eval_atom1604 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1604 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom1604, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1604_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203878555372800 : Int) atom1604) := by
  rw [SparsePolynomial.eval_scale, eval_atom1604]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1605 : SparsePolynomial.Poly := [([5,17,18], 1)]
theorem eval_atom1605 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1605 = ((g 5) * (g 17) * (g 18)) := by
  norm_num [atom1605, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1605_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (388206381024000 : Int) atom1605) := by
  rw [SparsePolynomial.eval_scale, eval_atom1605]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1606 : SparsePolynomial.Poly := [([5,17,19], 1)]
theorem eval_atom1606 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1606 = ((g 5) * (g 17) * (g 19)) := by
  norm_num [atom1606, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1606_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (382143218688000 : Int) atom1606) := by
  rw [SparsePolynomial.eval_scale, eval_atom1606]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1607 : SparsePolynomial.Poly := [([5,17,20], 1)]
theorem eval_atom1607 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1607 = ((g 5) * (g 17) * (g 20)) := by
  norm_num [atom1607, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1607_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (523631256825600 : Int) atom1607) := by
  rw [SparsePolynomial.eval_scale, eval_atom1607]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1608 : SparsePolynomial.Poly := [([5,17,21], 1)]
theorem eval_atom1608 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1608 = ((g 5) * (g 17) * (g 21)) := by
  norm_num [atom1608, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1608_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (536995434729600 : Int) atom1608) := by
  rw [SparsePolynomial.eval_scale, eval_atom1608]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1609 : SparsePolynomial.Poly := [([5,17,22], 1)]
theorem eval_atom1609 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1609 = ((g 5) * (g 17) * (g 22)) := by
  norm_num [atom1609, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1609_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (477639158169600 : Int) atom1609) := by
  rw [SparsePolynomial.eval_scale, eval_atom1609]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1610 : SparsePolynomial.Poly := [([5,17,23], 1)]
theorem eval_atom1610 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1610 = ((g 5) * (g 17) * (g 23)) := by
  norm_num [atom1610, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1610_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (626099548536000 : Int) atom1610) := by
  rw [SparsePolynomial.eval_scale, eval_atom1610]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1611 : SparsePolynomial.Poly := [([5,18,18], 1)]
theorem eval_atom1611 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1611 = ((g 5) * (g 18) * (g 18)) := by
  norm_num [atom1611, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1611_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (235368093945600 : Int) atom1611) := by
  rw [SparsePolynomial.eval_scale, eval_atom1611]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1612 : SparsePolynomial.Poly := [([5,18,19], 1)]
theorem eval_atom1612 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1612 = ((g 5) * (g 18) * (g 19)) := by
  norm_num [atom1612, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1612_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (440940625171200 : Int) atom1612) := by
  rw [SparsePolynomial.eval_scale, eval_atom1612]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1613 : SparsePolynomial.Poly := [([5,18,20], 1)]
theorem eval_atom1613 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1613 = ((g 5) * (g 18) * (g 20)) := by
  norm_num [atom1613, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1613_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (625762461139200 : Int) atom1613) := by
  rw [SparsePolynomial.eval_scale, eval_atom1613]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1614 : SparsePolynomial.Poly := [([5,18,21], 1)]
theorem eval_atom1614 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1614 = ((g 5) * (g 18) * (g 21)) := by
  norm_num [atom1614, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1614_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (603689881132800 : Int) atom1614) := by
  rw [SparsePolynomial.eval_scale, eval_atom1614]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1615 : SparsePolynomial.Poly := [([5,18,22], 1)]
theorem eval_atom1615 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1615 = ((g 5) * (g 18) * (g 22)) := by
  norm_num [atom1615, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1615_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (445497019027200 : Int) atom1615) := by
  rw [SparsePolynomial.eval_scale, eval_atom1615]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1616 : SparsePolynomial.Poly := [([5,18,23], 1)]
theorem eval_atom1616 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1616 = ((g 5) * (g 18) * (g 23)) := by
  norm_num [atom1616, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1616_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (623082726604800 : Int) atom1616) := by
  rw [SparsePolynomial.eval_scale, eval_atom1616]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1617 : SparsePolynomial.Poly := [([5,19,19], 1)]
theorem eval_atom1617 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1617 = ((g 5) * (g 19) * (g 19)) := by
  norm_num [atom1617, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1617_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159053271632640 : Int) atom1617) := by
  rw [SparsePolynomial.eval_scale, eval_atom1617]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1618 : SparsePolynomial.Poly := [([5,19,20], 1)]
theorem eval_atom1618 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1618 = ((g 5) * (g 19) * (g 20)) := by
  norm_num [atom1618, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1618_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (480885340320000 : Int) atom1618) := by
  rw [SparsePolynomial.eval_scale, eval_atom1618]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1619 : SparsePolynomial.Poly := [([5,19,21], 1)]
theorem eval_atom1619 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1619 = ((g 5) * (g 19) * (g 21)) := by
  norm_num [atom1619, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1619_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (470906173584000 : Int) atom1619) := by
  rw [SparsePolynomial.eval_scale, eval_atom1619]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1620 : SparsePolynomial.Poly := [([5,19,22], 1)]
theorem eval_atom1620 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1620 = ((g 5) * (g 19) * (g 22)) := by
  norm_num [atom1620, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1620_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (369833052153600 : Int) atom1620) := by
  rw [SparsePolynomial.eval_scale, eval_atom1620]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1621 : SparsePolynomial.Poly := [([5,19,23], 1)]
theorem eval_atom1621 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1621 = ((g 5) * (g 19) * (g 23)) := by
  norm_num [atom1621, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1621_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (416251856059200 : Int) atom1621) := by
  rw [SparsePolynomial.eval_scale, eval_atom1621]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1622 : SparsePolynomial.Poly := [([5,20,20], 1)]
theorem eval_atom1622 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1622 = ((g 5) * (g 20) * (g 20)) := by
  norm_num [atom1622, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1622_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (342379007308800 : Int) atom1622) := by
  rw [SparsePolynomial.eval_scale, eval_atom1622]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1623 : SparsePolynomial.Poly := [([5,20,21], 1)]
theorem eval_atom1623 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1623 = ((g 5) * (g 20) * (g 21)) := by
  norm_num [atom1623, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1623_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (509142662582400 : Int) atom1623) := by
  rw [SparsePolynomial.eval_scale, eval_atom1623]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1624 : SparsePolynomial.Poly := [([5,20,22], 1)]
theorem eval_atom1624 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1624 = ((g 5) * (g 20) * (g 22)) := by
  norm_num [atom1624, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1624_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (380139266304000 : Int) atom1624) := by
  rw [SparsePolynomial.eval_scale, eval_atom1624]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1625 : SparsePolynomial.Poly := [([5,20,23], 1)]
theorem eval_atom1625 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1625 = ((g 5) * (g 20) * (g 23)) := by
  norm_num [atom1625, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1625_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (433594128945600 : Int) atom1625) := by
  rw [SparsePolynomial.eval_scale, eval_atom1625]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1626 : SparsePolynomial.Poly := [([5,21,21], 1)]
theorem eval_atom1626 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1626 = ((g 5) * (g 21) * (g 21)) := by
  norm_num [atom1626, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1626_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125494567228800 : Int) atom1626) := by
  rw [SparsePolynomial.eval_scale, eval_atom1626]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1627 : SparsePolynomial.Poly := [([5,21,22], 1)]
theorem eval_atom1627 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1627 = ((g 5) * (g 21) * (g 22)) := by
  norm_num [atom1627, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1627_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175501668384000 : Int) atom1627) := by
  rw [SparsePolynomial.eval_scale, eval_atom1627]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1628 : SparsePolynomial.Poly := [([5,21,23], 1)]
theorem eval_atom1628 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1628 = ((g 5) * (g 21) * (g 23)) := by
  norm_num [atom1628, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1628_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230197672656000 : Int) atom1628) := by
  rw [SparsePolynomial.eval_scale, eval_atom1628]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1629 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom1629 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1629 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom1629, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1629_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19029802176000 : Int) atom1629) := by
  rw [SparsePolynomial.eval_scale, eval_atom1629]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1630 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom1630 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1630 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom1630, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1630_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29330228928000 : Int) atom1630) := by
  rw [SparsePolynomial.eval_scale, eval_atom1630]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1631 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom1631 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1631 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom1631, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1631_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7420559731200 : Int) atom1631) := by
  rw [SparsePolynomial.eval_scale, eval_atom1631]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1632 : SparsePolynomial.Poly := [([6,6,9], 1)]
theorem eval_atom1632 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1632 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom1632, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1632_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5145488409600 : Int) atom1632) := by
  rw [SparsePolynomial.eval_scale, eval_atom1632]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1633 : SparsePolynomial.Poly := [([6,6,10], 1)]
theorem eval_atom1633 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1633 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom1633, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1633_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7788087023904 : Int) atom1633) := by
  rw [SparsePolynomial.eval_scale, eval_atom1633]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1634 : SparsePolynomial.Poly := [([6,6,11], 1)]
theorem eval_atom1634 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1634 = ((g 6) * (g 6) * (g 11)) := by
  norm_num [atom1634, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1634_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2062447833600 : Int) atom1634) := by
  rw [SparsePolynomial.eval_scale, eval_atom1634]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1635 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom1635 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1635 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom1635, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1635_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26235375936000 : Int) atom1635) := by
  rw [SparsePolynomial.eval_scale, eval_atom1635]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1636 : SparsePolynomial.Poly := [([6,7,8], 1)]
theorem eval_atom1636 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1636 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom1636, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1636_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17921797555200 : Int) atom1636) := by
  rw [SparsePolynomial.eval_scale, eval_atom1636]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1637 : SparsePolynomial.Poly := [([6,7,10], 1)]
theorem eval_atom1637 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1637 = ((g 6) * (g 7) * (g 10)) := by
  norm_num [atom1637, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1637_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6305789971008 : Int) atom1637) := by
  rw [SparsePolynomial.eval_scale, eval_atom1637]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1638 : SparsePolynomial.Poly := [([6,7,12], 1)]
theorem eval_atom1638 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1638 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom1638, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1638_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1020592742400 : Int) atom1638) := by
  rw [SparsePolynomial.eval_scale, eval_atom1638]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1639 : SparsePolynomial.Poly := [([6,7,13], 1)]
theorem eval_atom1639 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1639 = ((g 6) * (g 7) * (g 13)) := by
  norm_num [atom1639, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1639_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4103633318400 : Int) atom1639) := by
  rw [SparsePolynomial.eval_scale, eval_atom1639]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1640 : SparsePolynomial.Poly := [([6,7,14], 1)]
theorem eval_atom1640 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1640 = ((g 6) * (g 7) * (g 14)) := by
  norm_num [atom1640, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1640_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7186673894400 : Int) atom1640) := by
  rw [SparsePolynomial.eval_scale, eval_atom1640]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1641 : SparsePolynomial.Poly := [([6,7,15], 1)]
theorem eval_atom1641 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1641 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom1641, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1641_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10269714470400 : Int) atom1641) := by
  rw [SparsePolynomial.eval_scale, eval_atom1641]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1642 : SparsePolynomial.Poly := [([6,7,16], 1)]
theorem eval_atom1642 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1642 = ((g 6) * (g 7) * (g 16)) := by
  norm_num [atom1642, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1642_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13352755046400 : Int) atom1642) := by
  rw [SparsePolynomial.eval_scale, eval_atom1642]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1643 : SparsePolynomial.Poly := [([6,7,17], 1)]
theorem eval_atom1643 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1643 = ((g 6) * (g 7) * (g 17)) := by
  norm_num [atom1643, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1643_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16435795622400 : Int) atom1643) := by
  rw [SparsePolynomial.eval_scale, eval_atom1643]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1644 : SparsePolynomial.Poly := [([6,7,18], 1)]
theorem eval_atom1644 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1644 = ((g 6) * (g 7) * (g 18)) := by
  norm_num [atom1644, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1644_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1333149269760 : Int) atom1644) := by
  rw [SparsePolynomial.eval_scale, eval_atom1644]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1645 : SparsePolynomial.Poly := [([6,7,21], 1)]
theorem eval_atom1645 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1645 = ((g 6) * (g 7) * (g 21)) := by
  norm_num [atom1645, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1645_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40850287632000 : Int) atom1645) := by
  rw [SparsePolynomial.eval_scale, eval_atom1645]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1646 : SparsePolynomial.Poly := [([6,7,22], 1)]
theorem eval_atom1646 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1646 = ((g 6) * (g 7) * (g 22)) := by
  norm_num [atom1646, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1646_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83033724533760 : Int) atom1646) := by
  rw [SparsePolynomial.eval_scale, eval_atom1646]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1647 : SparsePolynomial.Poly := [([6,7,23], 1)]
theorem eval_atom1647 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1647 = ((g 6) * (g 7) * (g 23)) := by
  norm_num [atom1647, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1647_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (133205957438400 : Int) atom1647) := by
  rw [SparsePolynomial.eval_scale, eval_atom1647]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1648 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom1648 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1648 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom1648, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1648_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17371338969600 : Int) atom1648) := by
  rw [SparsePolynomial.eval_scale, eval_atom1648]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block022 : SparsePolynomial.Poly := [([5,13,16], 245154757478400), ([5,13,17], 241242485299200), ([5,13,18], 297199359072000), ([5,13,19], 289024345209600), ([5,13,20], 399561282489600), ([5,13,21], 392412609388800), ([5,13,22], 462642209568000), ([5,13,23], 532871809747200), ([5,14,14], 150166318579200), ([5,14,15], 283120765804800), ([5,14,16], 274126792262400), ([5,14,17], 265132818720000), ([5,14,18], 302636058278400), ([5,14,19], 305305962746400), ([5,14,20], 417245094604800), ([5,14,21], 416219977958400), ([5,14,22], 472194345823200), ([5,14,23], 540748493762400), ([5,15,15], 174054567456000), ([5,15,16], 319660112217600), ([5,15,17], 304563844569600), ([5,15,18], 338015640211200), ([5,15,19], 327299245056000), ([5,15,20], 464134050374400), ([5,15,21], 469048055414400), ([5,15,22], 460158285888000), ([5,15,23], 521735242392000), ([5,16,16], 189788705568000), ([5,16,17], 354275216064000), ([5,16,18], 355661456774400), ([5,16,19], 344788493414400), ([5,16,20], 481466730528000), ([5,16,21], 489364229692800), ([5,16,22], 425664957312000), ([5,16,23], 568330230081600), ([5,17,17], 203878555372800), ([5,17,18], 388206381024000), ([5,17,19], 382143218688000), ([5,17,20], 523631256825600), ([5,17,21], 536995434729600), ([5,17,22], 477639158169600), ([5,17,23], 626099548536000), ([5,18,18], 235368093945600), ([5,18,19], 440940625171200), ([5,18,20], 625762461139200), ([5,18,21], 603689881132800), ([5,18,22], 445497019027200), ([5,18,23], 623082726604800), ([5,19,19], 159053271632640), ([5,19,20], 480885340320000), ([5,19,21], 470906173584000), ([5,19,22], 369833052153600), ([5,19,23], 416251856059200), ([5,20,20], 342379007308800), ([5,20,21], 509142662582400), ([5,20,22], 380139266304000), ([5,20,23], 433594128945600), ([5,21,21], 125494567228800), ([5,21,22], 175501668384000), ([5,21,23], 230197672656000), ([6,6,6], 19029802176000), ([6,6,7], 29330228928000), ([6,6,8], 7420559731200), ([6,6,9], 5145488409600), ([6,6,10], 7788087023904), ([6,6,11], 2062447833600), ([6,7,7], 26235375936000), ([6,7,8], 17921797555200), ([6,7,10], 6305789971008), ([6,7,12], 1020592742400), ([6,7,13], 4103633318400), ([6,7,14], 7186673894400), ([6,7,15], 10269714470400), ([6,7,16], 13352755046400), ([6,7,17], 16435795622400), ([6,7,18], 1333149269760), ([6,7,21], 40850287632000), ([6,7,22], 83033724533760), ([6,7,23], 133205957438400), ([6,8,8], 17371338969600)]
theorem block022_data : block022 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (245154757478400 : Int) atom1569) (SparsePolynomial.scale (241242485299200 : Int) atom1570)) (SparsePolynomial.merge (SparsePolynomial.scale (297199359072000 : Int) atom1571) (SparsePolynomial.merge (SparsePolynomial.scale (289024345209600 : Int) atom1572) (SparsePolynomial.scale (399561282489600 : Int) atom1573)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (392412609388800 : Int) atom1574) (SparsePolynomial.scale (462642209568000 : Int) atom1575)) (SparsePolynomial.merge (SparsePolynomial.scale (532871809747200 : Int) atom1576) (SparsePolynomial.merge (SparsePolynomial.scale (150166318579200 : Int) atom1577) (SparsePolynomial.scale (283120765804800 : Int) atom1578))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (274126792262400 : Int) atom1579) (SparsePolynomial.scale (265132818720000 : Int) atom1580)) (SparsePolynomial.merge (SparsePolynomial.scale (302636058278400 : Int) atom1581) (SparsePolynomial.merge (SparsePolynomial.scale (305305962746400 : Int) atom1582) (SparsePolynomial.scale (417245094604800 : Int) atom1583)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (416219977958400 : Int) atom1584) (SparsePolynomial.scale (472194345823200 : Int) atom1585)) (SparsePolynomial.merge (SparsePolynomial.scale (540748493762400 : Int) atom1586) (SparsePolynomial.merge (SparsePolynomial.scale (174054567456000 : Int) atom1587) (SparsePolynomial.scale (319660112217600 : Int) atom1588)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (304563844569600 : Int) atom1589) (SparsePolynomial.scale (338015640211200 : Int) atom1590)) (SparsePolynomial.merge (SparsePolynomial.scale (327299245056000 : Int) atom1591) (SparsePolynomial.merge (SparsePolynomial.scale (464134050374400 : Int) atom1592) (SparsePolynomial.scale (469048055414400 : Int) atom1593)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (460158285888000 : Int) atom1594) (SparsePolynomial.scale (521735242392000 : Int) atom1595)) (SparsePolynomial.merge (SparsePolynomial.scale (189788705568000 : Int) atom1596) (SparsePolynomial.merge (SparsePolynomial.scale (354275216064000 : Int) atom1597) (SparsePolynomial.scale (355661456774400 : Int) atom1598))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (344788493414400 : Int) atom1599) (SparsePolynomial.scale (481466730528000 : Int) atom1600)) (SparsePolynomial.merge (SparsePolynomial.scale (489364229692800 : Int) atom1601) (SparsePolynomial.merge (SparsePolynomial.scale (425664957312000 : Int) atom1602) (SparsePolynomial.scale (568330230081600 : Int) atom1603)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (203878555372800 : Int) atom1604) (SparsePolynomial.scale (388206381024000 : Int) atom1605)) (SparsePolynomial.merge (SparsePolynomial.scale (382143218688000 : Int) atom1606) (SparsePolynomial.merge (SparsePolynomial.scale (523631256825600 : Int) atom1607) (SparsePolynomial.scale (536995434729600 : Int) atom1608))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (477639158169600 : Int) atom1609) (SparsePolynomial.scale (626099548536000 : Int) atom1610)) (SparsePolynomial.merge (SparsePolynomial.scale (235368093945600 : Int) atom1611) (SparsePolynomial.merge (SparsePolynomial.scale (440940625171200 : Int) atom1612) (SparsePolynomial.scale (625762461139200 : Int) atom1613)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (603689881132800 : Int) atom1614) (SparsePolynomial.scale (445497019027200 : Int) atom1615)) (SparsePolynomial.merge (SparsePolynomial.scale (623082726604800 : Int) atom1616) (SparsePolynomial.merge (SparsePolynomial.scale (159053271632640 : Int) atom1617) (SparsePolynomial.scale (480885340320000 : Int) atom1618))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (470906173584000 : Int) atom1619) (SparsePolynomial.scale (369833052153600 : Int) atom1620)) (SparsePolynomial.merge (SparsePolynomial.scale (416251856059200 : Int) atom1621) (SparsePolynomial.merge (SparsePolynomial.scale (342379007308800 : Int) atom1622) (SparsePolynomial.scale (509142662582400 : Int) atom1623)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (380139266304000 : Int) atom1624) (SparsePolynomial.scale (433594128945600 : Int) atom1625)) (SparsePolynomial.merge (SparsePolynomial.scale (125494567228800 : Int) atom1626) (SparsePolynomial.merge (SparsePolynomial.scale (175501668384000 : Int) atom1627) (SparsePolynomial.scale (230197672656000 : Int) atom1628)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19029802176000 : Int) atom1629) (SparsePolynomial.scale (29330228928000 : Int) atom1630)) (SparsePolynomial.merge (SparsePolynomial.scale (7420559731200 : Int) atom1631) (SparsePolynomial.merge (SparsePolynomial.scale (5145488409600 : Int) atom1632) (SparsePolynomial.scale (7788087023904 : Int) atom1633)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2062447833600 : Int) atom1634) (SparsePolynomial.scale (26235375936000 : Int) atom1635)) (SparsePolynomial.merge (SparsePolynomial.scale (17921797555200 : Int) atom1636) (SparsePolynomial.merge (SparsePolynomial.scale (6305789971008 : Int) atom1637) (SparsePolynomial.scale (1020592742400 : Int) atom1638))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4103633318400 : Int) atom1639) (SparsePolynomial.scale (7186673894400 : Int) atom1640)) (SparsePolynomial.merge (SparsePolynomial.scale (10269714470400 : Int) atom1641) (SparsePolynomial.merge (SparsePolynomial.scale (13352755046400 : Int) atom1642) (SparsePolynomial.scale (16435795622400 : Int) atom1643)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1333149269760 : Int) atom1644) (SparsePolynomial.scale (40850287632000 : Int) atom1645)) (SparsePolynomial.merge (SparsePolynomial.scale (83033724533760 : Int) atom1646) (SparsePolynomial.merge (SparsePolynomial.scale (133205957438400 : Int) atom1647) (SparsePolynomial.scale (17371338969600 : Int) atom1648)))))))) := by decide +kernel
theorem block022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block022 := by
  rw [block022_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1569_nonneg g hg hA hB) (atom1570_nonneg g hg hA hB)) (add_nonneg (atom1571_nonneg g hg hA hB) (add_nonneg (atom1572_nonneg g hg hA hB) (atom1573_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1574_nonneg g hg hA hB) (atom1575_nonneg g hg hA hB)) (add_nonneg (atom1576_nonneg g hg hA hB) (add_nonneg (atom1577_nonneg g hg hA hB) (atom1578_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1579_nonneg g hg hA hB) (atom1580_nonneg g hg hA hB)) (add_nonneg (atom1581_nonneg g hg hA hB) (add_nonneg (atom1582_nonneg g hg hA hB) (atom1583_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1584_nonneg g hg hA hB) (atom1585_nonneg g hg hA hB)) (add_nonneg (atom1586_nonneg g hg hA hB) (add_nonneg (atom1587_nonneg g hg hA hB) (atom1588_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1589_nonneg g hg hA hB) (atom1590_nonneg g hg hA hB)) (add_nonneg (atom1591_nonneg g hg hA hB) (add_nonneg (atom1592_nonneg g hg hA hB) (atom1593_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1594_nonneg g hg hA hB) (atom1595_nonneg g hg hA hB)) (add_nonneg (atom1596_nonneg g hg hA hB) (add_nonneg (atom1597_nonneg g hg hA hB) (atom1598_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1599_nonneg g hg hA hB) (atom1600_nonneg g hg hA hB)) (add_nonneg (atom1601_nonneg g hg hA hB) (add_nonneg (atom1602_nonneg g hg hA hB) (atom1603_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1604_nonneg g hg hA hB) (atom1605_nonneg g hg hA hB)) (add_nonneg (atom1606_nonneg g hg hA hB) (add_nonneg (atom1607_nonneg g hg hA hB) (atom1608_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1609_nonneg g hg hA hB) (atom1610_nonneg g hg hA hB)) (add_nonneg (atom1611_nonneg g hg hA hB) (add_nonneg (atom1612_nonneg g hg hA hB) (atom1613_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1614_nonneg g hg hA hB) (atom1615_nonneg g hg hA hB)) (add_nonneg (atom1616_nonneg g hg hA hB) (add_nonneg (atom1617_nonneg g hg hA hB) (atom1618_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1619_nonneg g hg hA hB) (atom1620_nonneg g hg hA hB)) (add_nonneg (atom1621_nonneg g hg hA hB) (add_nonneg (atom1622_nonneg g hg hA hB) (atom1623_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1624_nonneg g hg hA hB) (atom1625_nonneg g hg hA hB)) (add_nonneg (atom1626_nonneg g hg hA hB) (add_nonneg (atom1627_nonneg g hg hA hB) (atom1628_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1629_nonneg g hg hA hB) (atom1630_nonneg g hg hA hB)) (add_nonneg (atom1631_nonneg g hg hA hB) (add_nonneg (atom1632_nonneg g hg hA hB) (atom1633_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1634_nonneg g hg hA hB) (atom1635_nonneg g hg hA hB)) (add_nonneg (atom1636_nonneg g hg hA hB) (add_nonneg (atom1637_nonneg g hg hA hB) (atom1638_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1639_nonneg g hg hA hB) (atom1640_nonneg g hg hA hB)) (add_nonneg (atom1641_nonneg g hg hA hB) (add_nonneg (atom1642_nonneg g hg hA hB) (atom1643_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1644_nonneg g hg hA hB) (atom1645_nonneg g hg hA hB)) (add_nonneg (atom1646_nonneg g hg hA hB) (add_nonneg (atom1647_nonneg g hg hA hB) (atom1648_nonneg g hg hA hB))))))))

end APPT.Finite24
