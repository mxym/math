import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1536 : SparsePolynomial.Poly := [([10,12,17], 1)]
theorem eval_atom1536 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1536 = ((g 10) * (g 12) * (g 17)) := by
  norm_num [atom1536, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1536_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12235036884000 : Int) atom1536) := by
  rw [SparsePolynomial.eval_scale, eval_atom1536]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1537 : SparsePolynomial.Poly := [([10,12,18], 1)]
theorem eval_atom1537 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1537 = ((g 10) * (g 12) * (g 18)) := by
  norm_num [atom1537, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1537_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10060008291200 : Int) atom1537) := by
  rw [SparsePolynomial.eval_scale, eval_atom1537]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1538 : SparsePolynomial.Poly := [([10,12,19], 1)]
theorem eval_atom1538 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1538 = ((g 10) * (g 12) * (g 19)) := by
  norm_num [atom1538, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1538_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19067301227520 : Int) atom1538) := by
  rw [SparsePolynomial.eval_scale, eval_atom1538]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1539 : SparsePolynomial.Poly := [([10,12,20], 1)]
theorem eval_atom1539 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1539 = ((g 10) * (g 12) * (g 20)) := by
  norm_num [atom1539, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1539_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30545055374400 : Int) atom1539) := by
  rw [SparsePolynomial.eval_scale, eval_atom1539]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1540 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom1540 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1540 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom1540, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1540_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3637196294400 : Int) atom1540) := by
  rw [SparsePolynomial.eval_scale, eval_atom1540]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1541 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom1541 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1541 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom1541, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1541_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6880901068800 : Int) atom1541) := by
  rw [SparsePolynomial.eval_scale, eval_atom1541]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1542 : SparsePolynomial.Poly := [([10,13,15], 1)]
theorem eval_atom1542 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1542 = ((g 10) * (g 13) * (g 15)) := by
  norm_num [atom1542, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1542_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8610848568000 : Int) atom1542) := by
  rw [SparsePolynomial.eval_scale, eval_atom1542]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1543 : SparsePolynomial.Poly := [([10,13,16], 1)]
theorem eval_atom1543 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1543 = ((g 10) * (g 13) * (g 16)) := by
  norm_num [atom1543, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1543_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7226753652000 : Int) atom1543) := by
  rw [SparsePolynomial.eval_scale, eval_atom1543]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1544 : SparsePolynomial.Poly := [([10,13,17], 1)]
theorem eval_atom1544 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1544 = ((g 10) * (g 13) * (g 17)) := by
  norm_num [atom1544, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1544_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24723029116800 : Int) atom1544) := by
  rw [SparsePolynomial.eval_scale, eval_atom1544]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1545 : SparsePolynomial.Poly := [([10,13,18], 1)]
theorem eval_atom1545 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1545 = ((g 10) * (g 13) * (g 18)) := by
  norm_num [atom1545, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1545_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25487556040800 : Int) atom1545) := by
  rw [SparsePolynomial.eval_scale, eval_atom1545]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1546 : SparsePolynomial.Poly := [([10,13,19], 1)]
theorem eval_atom1546 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1546 = ((g 10) * (g 13) * (g 19)) := by
  norm_num [atom1546, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1546_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29609621330400 : Int) atom1546) := by
  rw [SparsePolynomial.eval_scale, eval_atom1546]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1547 : SparsePolynomial.Poly := [([10,13,20], 1)]
theorem eval_atom1547 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1547 = ((g 10) * (g 13) * (g 20)) := by
  norm_num [atom1547, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1547_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48203677670400 : Int) atom1547) := by
  rw [SparsePolynomial.eval_scale, eval_atom1547]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1548 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom1548 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1548 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom1548, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1548_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7524616377600 : Int) atom1548) := by
  rw [SparsePolynomial.eval_scale, eval_atom1548]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1549 : SparsePolynomial.Poly := [([10,14,15], 1)]
theorem eval_atom1549 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1549 = ((g 10) * (g 14) * (g 15)) := by
  norm_num [atom1549, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1549_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13837762108800 : Int) atom1549) := by
  rw [SparsePolynomial.eval_scale, eval_atom1549]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1550 : SparsePolynomial.Poly := [([10,14,16], 1)]
theorem eval_atom1550 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1550 = ((g 10) * (g 14) * (g 16)) := by
  norm_num [atom1550, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1550_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14444665250400 : Int) atom1550) := by
  rw [SparsePolynomial.eval_scale, eval_atom1550]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1551 : SparsePolynomial.Poly := [([10,14,17], 1)]
theorem eval_atom1551 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1551 = ((g 10) * (g 14) * (g 17)) := by
  norm_num [atom1551, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1551_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39514858588800 : Int) atom1551) := by
  rw [SparsePolynomial.eval_scale, eval_atom1551]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1552 : SparsePolynomial.Poly := [([10,14,18], 1)]
theorem eval_atom1552 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1552 = ((g 10) * (g 14) * (g 18)) := by
  norm_num [atom1552, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1552_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43438294015200 : Int) atom1552) := by
  rw [SparsePolynomial.eval_scale, eval_atom1552]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1553 : SparsePolynomial.Poly := [([10,14,19], 1)]
theorem eval_atom1553 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1553 = ((g 10) * (g 14) * (g 19)) := by
  norm_num [atom1553, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1553_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44668852452000 : Int) atom1553) := by
  rw [SparsePolynomial.eval_scale, eval_atom1553]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1554 : SparsePolynomial.Poly := [([10,14,20], 1)]
theorem eval_atom1554 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1554 = ((g 10) * (g 14) * (g 20)) := by
  norm_num [atom1554, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1554_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70445302603200 : Int) atom1554) := by
  rw [SparsePolynomial.eval_scale, eval_atom1554]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1555 : SparsePolynomial.Poly := [([10,15,15], 1)]
theorem eval_atom1555 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1555 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom1555, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1555_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14207114880000 : Int) atom1555) := by
  rw [SparsePolynomial.eval_scale, eval_atom1555]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1556 : SparsePolynomial.Poly := [([10,15,16], 1)]
theorem eval_atom1556 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1556 = ((g 10) * (g 15) * (g 16)) := by
  norm_num [atom1556, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1556_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31648905514800 : Int) atom1556) := by
  rw [SparsePolynomial.eval_scale, eval_atom1556]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1557 : SparsePolynomial.Poly := [([10,15,17], 1)]
theorem eval_atom1557 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1557 = ((g 10) * (g 15) * (g 17)) := by
  norm_num [atom1557, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1557_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63044385868800 : Int) atom1557) := by
  rw [SparsePolynomial.eval_scale, eval_atom1557]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1558 : SparsePolynomial.Poly := [([10,15,18], 1)]
theorem eval_atom1558 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1558 = ((g 10) * (g 15) * (g 18)) := by
  norm_num [atom1558, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1558_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68251193312400 : Int) atom1558) := by
  rw [SparsePolynomial.eval_scale, eval_atom1558]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1559 : SparsePolynomial.Poly := [([10,15,19], 1)]
theorem eval_atom1559 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1559 = ((g 10) * (g 15) * (g 19)) := by
  norm_num [atom1559, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1559_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52704630997200 : Int) atom1559) := by
  rw [SparsePolynomial.eval_scale, eval_atom1559]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1560 : SparsePolynomial.Poly := [([10,15,20], 1)]
theorem eval_atom1560 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1560 = ((g 10) * (g 15) * (g 20)) := by
  norm_num [atom1560, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1560_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (84534447690000 : Int) atom1560) := by
  rw [SparsePolynomial.eval_scale, eval_atom1560]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1561 : SparsePolynomial.Poly := [([10,16,16], 1)]
theorem eval_atom1561 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1561 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom1561, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1561_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13258427535360 : Int) atom1561) := by
  rw [SparsePolynomial.eval_scale, eval_atom1561]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1562 : SparsePolynomial.Poly := [([10,16,17], 1)]
theorem eval_atom1562 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1562 = ((g 10) * (g 16) * (g 17)) := by
  norm_num [atom1562, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1562_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55380479086800 : Int) atom1562) := by
  rw [SparsePolynomial.eval_scale, eval_atom1562]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1563 : SparsePolynomial.Poly := [([10,16,18], 1)]
theorem eval_atom1563 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1563 = ((g 10) * (g 16) * (g 18)) := by
  norm_num [atom1563, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1563_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (67640031660600 : Int) atom1563) := by
  rw [SparsePolynomial.eval_scale, eval_atom1563]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1564 : SparsePolynomial.Poly := [([10,16,19], 1)]
theorem eval_atom1564 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1564 = ((g 10) * (g 16) * (g 19)) := by
  norm_num [atom1564, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1564_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51789484202400 : Int) atom1564) := by
  rw [SparsePolynomial.eval_scale, eval_atom1564]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1565 : SparsePolynomial.Poly := [([10,16,20], 1)]
theorem eval_atom1565 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1565 = ((g 10) * (g 16) * (g 20)) := by
  norm_num [atom1565, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1565_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71505263913300 : Int) atom1565) := by
  rw [SparsePolynomial.eval_scale, eval_atom1565]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1566 : SparsePolynomial.Poly := [([10,17,17], 1)]
theorem eval_atom1566 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1566 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom1566, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1566_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41806301644800 : Int) atom1566) := by
  rw [SparsePolynomial.eval_scale, eval_atom1566]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1567 : SparsePolynomial.Poly := [([10,17,18], 1)]
theorem eval_atom1567 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1567 = ((g 10) * (g 17) * (g 18)) := by
  norm_num [atom1567, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1567_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79803065286000 : Int) atom1567) := by
  rw [SparsePolynomial.eval_scale, eval_atom1567]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1568 : SparsePolynomial.Poly := [([10,17,19], 1)]
theorem eval_atom1568 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1568 = ((g 10) * (g 17) * (g 19)) := by
  norm_num [atom1568, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1568_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57575234833200 : Int) atom1568) := by
  rw [SparsePolynomial.eval_scale, eval_atom1568]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1569 : SparsePolynomial.Poly := [([10,17,20], 1)]
theorem eval_atom1569 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1569 = ((g 10) * (g 17) * (g 20)) := by
  norm_num [atom1569, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1569_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64172281244400 : Int) atom1569) := by
  rw [SparsePolynomial.eval_scale, eval_atom1569]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1570 : SparsePolynomial.Poly := [([10,18,18], 1)]
theorem eval_atom1570 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1570 = ((g 10) * (g 18) * (g 18)) := by
  norm_num [atom1570, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1570_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32379144373800 : Int) atom1570) := by
  rw [SparsePolynomial.eval_scale, eval_atom1570]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1571 : SparsePolynomial.Poly := [([10,18,19], 1)]
theorem eval_atom1571 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1571 = ((g 10) * (g 18) * (g 19)) := by
  norm_num [atom1571, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1571_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46613159346600 : Int) atom1571) := by
  rw [SparsePolynomial.eval_scale, eval_atom1571]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1572 : SparsePolynomial.Poly := [([10,18,20], 1)]
theorem eval_atom1572 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1572 = ((g 10) * (g 18) * (g 20)) := by
  norm_num [atom1572, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1572_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56384774100900 : Int) atom1572) := by
  rw [SparsePolynomial.eval_scale, eval_atom1572]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1573 : SparsePolynomial.Poly := [([10,19,19], 1)]
theorem eval_atom1573 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1573 = ((g 10) * (g 19) * (g 19)) := by
  norm_num [atom1573, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1573_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9434482696800 : Int) atom1573) := by
  rw [SparsePolynomial.eval_scale, eval_atom1573]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1574 : SparsePolynomial.Poly := [([10,19,20], 1)]
theorem eval_atom1574 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1574 = ((g 10) * (g 19) * (g 20)) := by
  norm_num [atom1574, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1574_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29846674802700 : Int) atom1574) := by
  rw [SparsePolynomial.eval_scale, eval_atom1574]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1575 : SparsePolynomial.Poly := [([10,20,20], 1)]
theorem eval_atom1575 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1575 = ((g 10) * (g 20) * (g 20)) := by
  norm_num [atom1575, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1575_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16605245065500 : Int) atom1575) := by
  rw [SparsePolynomial.eval_scale, eval_atom1575]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1576 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom1576 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1576 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom1576, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1576_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (625628505600 : Int) atom1576) := by
  rw [SparsePolynomial.eval_scale, eval_atom1576]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1577 : SparsePolynomial.Poly := [([11,11,15], 1)]
theorem eval_atom1577 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1577 = ((g 11) * (g 11) * (g 15)) := by
  norm_num [atom1577, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1577_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3027061094400 : Int) atom1577) := by
  rw [SparsePolynomial.eval_scale, eval_atom1577]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1578 : SparsePolynomial.Poly := [([11,11,17], 1)]
theorem eval_atom1578 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1578 = ((g 11) * (g 11) * (g 17)) := by
  norm_num [atom1578, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1578_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4622441241600 : Int) atom1578) := by
  rw [SparsePolynomial.eval_scale, eval_atom1578]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1579 : SparsePolynomial.Poly := [([11,12,14], 1)]
theorem eval_atom1579 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1579 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom1579, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1579_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (427179916800 : Int) atom1579) := by
  rw [SparsePolynomial.eval_scale, eval_atom1579]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1580 : SparsePolynomial.Poly := [([11,12,15], 1)]
theorem eval_atom1580 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1580 = ((g 11) * (g 12) * (g 15)) := by
  norm_num [atom1580, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1580_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2412192625920 : Int) atom1580) := by
  rw [SparsePolynomial.eval_scale, eval_atom1580]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1581 : SparsePolynomial.Poly := [([11,12,17], 1)]
theorem eval_atom1581 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1581 = ((g 11) * (g 12) * (g 17)) := by
  norm_num [atom1581, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1581_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12512392569600 : Int) atom1581) := by
  rw [SparsePolynomial.eval_scale, eval_atom1581]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1582 : SparsePolynomial.Poly := [([11,12,18], 1)]
theorem eval_atom1582 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1582 = ((g 11) * (g 12) * (g 18)) := by
  norm_num [atom1582, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1582_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6764344227200 : Int) atom1582) := by
  rw [SparsePolynomial.eval_scale, eval_atom1582]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1583 : SparsePolynomial.Poly := [([11,12,19], 1)]
theorem eval_atom1583 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1583 = ((g 11) * (g 12) * (g 19)) := by
  norm_num [atom1583, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1583_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11598417976320 : Int) atom1583) := by
  rw [SparsePolynomial.eval_scale, eval_atom1583]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1584 : SparsePolynomial.Poly := [([11,12,20], 1)]
theorem eval_atom1584 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1584 = ((g 11) * (g 12) * (g 20)) := by
  norm_num [atom1584, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1584_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17871729019200 : Int) atom1584) := by
  rw [SparsePolynomial.eval_scale, eval_atom1584]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1585 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom1585 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1585 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom1585, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1585_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1585379635200 : Int) atom1585) := by
  rw [SparsePolynomial.eval_scale, eval_atom1585]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1586 : SparsePolynomial.Poly := [([11,13,14], 1)]
theorem eval_atom1586 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1586 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom1586, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1586_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2686419532800 : Int) atom1586) := by
  rw [SparsePolynomial.eval_scale, eval_atom1586]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1587 : SparsePolynomial.Poly := [([11,13,15], 1)]
theorem eval_atom1587 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1587 = ((g 11) * (g 13) * (g 15)) := by
  norm_num [atom1587, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1587_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2932238030400 : Int) atom1587) := by
  rw [SparsePolynomial.eval_scale, eval_atom1587]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1588 : SparsePolynomial.Poly := [([11,13,16], 1)]
theorem eval_atom1588 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1588 = ((g 11) * (g 13) * (g 16)) := by
  norm_num [atom1588, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1588_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229178692800 : Int) atom1588) := by
  rw [SparsePolynomial.eval_scale, eval_atom1588]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1589 : SparsePolynomial.Poly := [([11,13,17], 1)]
theorem eval_atom1589 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1589 = ((g 11) * (g 13) * (g 17)) := by
  norm_num [atom1589, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1589_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18882297907200 : Int) atom1589) := by
  rw [SparsePolynomial.eval_scale, eval_atom1589]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1590 : SparsePolynomial.Poly := [([11,13,18], 1)]
theorem eval_atom1590 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1590 = ((g 11) * (g 13) * (g 18)) := by
  norm_num [atom1590, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1590_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16597632038400 : Int) atom1590) := by
  rw [SparsePolynomial.eval_scale, eval_atom1590]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1591 : SparsePolynomial.Poly := [([11,13,19], 1)]
theorem eval_atom1591 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1591 = ((g 11) * (g 13) * (g 19)) := by
  norm_num [atom1591, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1591_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20194842312000 : Int) atom1591) := by
  rw [SparsePolynomial.eval_scale, eval_atom1591]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1592 : SparsePolynomial.Poly := [([11,13,20], 1)]
theorem eval_atom1592 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1592 = ((g 11) * (g 13) * (g 20)) := by
  norm_num [atom1592, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1592_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38617257772800 : Int) atom1592) := by
  rw [SparsePolynomial.eval_scale, eval_atom1592]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1593 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom1593 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1593 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom1593, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1593_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4954771584000 : Int) atom1593) := by
  rw [SparsePolynomial.eval_scale, eval_atom1593]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1594 : SparsePolynomial.Poly := [([11,14,15], 1)]
theorem eval_atom1594 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1594 = ((g 11) * (g 14) * (g 15)) := by
  norm_num [atom1594, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1594_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8093431584000 : Int) atom1594) := by
  rw [SparsePolynomial.eval_scale, eval_atom1594]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1595 : SparsePolynomial.Poly := [([11,14,16], 1)]
theorem eval_atom1595 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1595 = ((g 11) * (g 14) * (g 16)) := by
  norm_num [atom1595, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1595_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8260858368000 : Int) atom1595) := by
  rw [SparsePolynomial.eval_scale, eval_atom1595]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1596 : SparsePolynomial.Poly := [([11,14,17], 1)]
theorem eval_atom1596 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1596 = ((g 11) * (g 14) * (g 17)) := by
  norm_num [atom1596, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1596_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35367383520000 : Int) atom1596) := by
  rw [SparsePolynomial.eval_scale, eval_atom1596]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1597 : SparsePolynomial.Poly := [([11,14,18], 1)]
theorem eval_atom1597 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1597 = ((g 11) * (g 14) * (g 18)) := by
  norm_num [atom1597, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1597_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36765453110400 : Int) atom1597) := by
  rw [SparsePolynomial.eval_scale, eval_atom1597]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1598 : SparsePolynomial.Poly := [([11,14,19], 1)]
theorem eval_atom1598 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1598 = ((g 11) * (g 14) * (g 19)) := by
  norm_num [atom1598, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1598_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37994983488000 : Int) atom1598) := by
  rw [SparsePolynomial.eval_scale, eval_atom1598]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1599 : SparsePolynomial.Poly := [([11,14,20], 1)]
theorem eval_atom1599 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1599 = ((g 11) * (g 14) * (g 20)) := by
  norm_num [atom1599, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1599_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63945789163200 : Int) atom1599) := by
  rw [SparsePolynomial.eval_scale, eval_atom1599]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1600 : SparsePolynomial.Poly := [([11,15,15], 1)]
theorem eval_atom1600 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1600 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom1600, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1600_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11306983564800 : Int) atom1600) := by
  rw [SparsePolynomial.eval_scale, eval_atom1600]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1601 : SparsePolynomial.Poly := [([11,15,16], 1)]
theorem eval_atom1601 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1601 = ((g 11) * (g 15) * (g 16)) := by
  norm_num [atom1601, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1601_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26897818752000 : Int) atom1601) := by
  rw [SparsePolynomial.eval_scale, eval_atom1601]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1602 : SparsePolynomial.Poly := [([11,15,17], 1)]
theorem eval_atom1602 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1602 = ((g 11) * (g 15) * (g 17)) := by
  norm_num [atom1602, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1602_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60580379059200 : Int) atom1602) := by
  rw [SparsePolynomial.eval_scale, eval_atom1602]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1603 : SparsePolynomial.Poly := [([11,15,18], 1)]
theorem eval_atom1603 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1603 = ((g 11) * (g 15) * (g 18)) := by
  norm_num [atom1603, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1603_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65618034048000 : Int) atom1603) := by
  rw [SparsePolynomial.eval_scale, eval_atom1603]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1604 : SparsePolynomial.Poly := [([11,15,19], 1)]
theorem eval_atom1604 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1604 = ((g 11) * (g 15) * (g 19)) := by
  norm_num [atom1604, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1604_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51049231833600 : Int) atom1604) := by
  rw [SparsePolynomial.eval_scale, eval_atom1604]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1605 : SparsePolynomial.Poly := [([11,15,20], 1)]
theorem eval_atom1605 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1605 = ((g 11) * (g 15) * (g 20)) := by
  norm_num [atom1605, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1605_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83972064960000 : Int) atom1605) := by
  rw [SparsePolynomial.eval_scale, eval_atom1605]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1606 : SparsePolynomial.Poly := [([11,16,16], 1)]
theorem eval_atom1606 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1606 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom1606, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1606_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11599244213760 : Int) atom1606) := by
  rw [SparsePolynomial.eval_scale, eval_atom1606]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1607 : SparsePolynomial.Poly := [([11,16,17], 1)]
theorem eval_atom1607 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1607 = ((g 11) * (g 16) * (g 17)) := by
  norm_num [atom1607, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1607_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54517358246400 : Int) atom1607) := by
  rw [SparsePolynomial.eval_scale, eval_atom1607]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1608 : SparsePolynomial.Poly := [([11,16,18], 1)]
theorem eval_atom1608 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1608 = ((g 11) * (g 16) * (g 18)) := by
  norm_num [atom1608, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1608_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68922680601600 : Int) atom1608) := by
  rw [SparsePolynomial.eval_scale, eval_atom1608]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1609 : SparsePolynomial.Poly := [([11,16,19], 1)]
theorem eval_atom1609 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1609 = ((g 11) * (g 16) * (g 19)) := by
  norm_num [atom1609, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1609_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54987390259200 : Int) atom1609) := by
  rw [SparsePolynomial.eval_scale, eval_atom1609]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1610 : SparsePolynomial.Poly := [([11,16,20], 1)]
theorem eval_atom1610 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1610 = ((g 11) * (g 16) * (g 20)) := by
  norm_num [atom1610, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1610_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76694201740800 : Int) atom1610) := by
  rw [SparsePolynomial.eval_scale, eval_atom1610]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1611 : SparsePolynomial.Poly := [([11,17,17], 1)]
theorem eval_atom1611 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1611 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom1611, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1611_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41556232166400 : Int) atom1611) := by
  rw [SparsePolynomial.eval_scale, eval_atom1611]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1612 : SparsePolynomial.Poly := [([11,17,18], 1)]
theorem eval_atom1612 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1612 = ((g 11) * (g 17) * (g 18)) := by
  norm_num [atom1612, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1612_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83144666304000 : Int) atom1612) := by
  rw [SparsePolynomial.eval_scale, eval_atom1612]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1613 : SparsePolynomial.Poly := [([11,17,19], 1)]
theorem eval_atom1613 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1613 = ((g 11) * (g 17) * (g 19)) := by
  norm_num [atom1613, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1613_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63150637939200 : Int) atom1613) := by
  rw [SparsePolynomial.eval_scale, eval_atom1613]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1614 : SparsePolynomial.Poly := [([11,17,20], 1)]
theorem eval_atom1614 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1614 = ((g 11) * (g 17) * (g 20)) := by
  norm_num [atom1614, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1614_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71866230105600 : Int) atom1614) := by
  rw [SparsePolynomial.eval_scale, eval_atom1614]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1615 : SparsePolynomial.Poly := [([11,18,18], 1)]
theorem eval_atom1615 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1615 = ((g 11) * (g 18) * (g 18)) := by
  norm_num [atom1615, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1615_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36462275136000 : Int) atom1615) := by
  rw [SparsePolynomial.eval_scale, eval_atom1615]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block021 : SparsePolynomial.Poly := [([10,12,17], 12235036884000), ([10,12,18], 10060008291200), ([10,12,19], 19067301227520), ([10,12,20], 30545055374400), ([10,13,13], 3637196294400), ([10,13,14], 6880901068800), ([10,13,15], 8610848568000), ([10,13,16], 7226753652000), ([10,13,17], 24723029116800), ([10,13,18], 25487556040800), ([10,13,19], 29609621330400), ([10,13,20], 48203677670400), ([10,14,14], 7524616377600), ([10,14,15], 13837762108800), ([10,14,16], 14444665250400), ([10,14,17], 39514858588800), ([10,14,18], 43438294015200), ([10,14,19], 44668852452000), ([10,14,20], 70445302603200), ([10,15,15], 14207114880000), ([10,15,16], 31648905514800), ([10,15,17], 63044385868800), ([10,15,18], 68251193312400), ([10,15,19], 52704630997200), ([10,15,20], 84534447690000), ([10,16,16], 13258427535360), ([10,16,17], 55380479086800), ([10,16,18], 67640031660600), ([10,16,19], 51789484202400), ([10,16,20], 71505263913300), ([10,17,17], 41806301644800), ([10,17,18], 79803065286000), ([10,17,19], 57575234833200), ([10,17,20], 64172281244400), ([10,18,18], 32379144373800), ([10,18,19], 46613159346600), ([10,18,20], 56384774100900), ([10,19,19], 9434482696800), ([10,19,20], 29846674802700), ([10,20,20], 16605245065500), ([11,11,11], 625628505600), ([11,11,15], 3027061094400), ([11,11,17], 4622441241600), ([11,12,14], 427179916800), ([11,12,15], 2412192625920), ([11,12,17], 12512392569600), ([11,12,18], 6764344227200), ([11,12,19], 11598417976320), ([11,12,20], 17871729019200), ([11,13,13], 1585379635200), ([11,13,14], 2686419532800), ([11,13,15], 2932238030400), ([11,13,16], 229178692800), ([11,13,17], 18882297907200), ([11,13,18], 16597632038400), ([11,13,19], 20194842312000), ([11,13,20], 38617257772800), ([11,14,14], 4954771584000), ([11,14,15], 8093431584000), ([11,14,16], 8260858368000), ([11,14,17], 35367383520000), ([11,14,18], 36765453110400), ([11,14,19], 37994983488000), ([11,14,20], 63945789163200), ([11,15,15], 11306983564800), ([11,15,16], 26897818752000), ([11,15,17], 60580379059200), ([11,15,18], 65618034048000), ([11,15,19], 51049231833600), ([11,15,20], 83972064960000), ([11,16,16], 11599244213760), ([11,16,17], 54517358246400), ([11,16,18], 68922680601600), ([11,16,19], 54987390259200), ([11,16,20], 76694201740800), ([11,17,17], 41556232166400), ([11,17,18], 83144666304000), ([11,17,19], 63150637939200), ([11,17,20], 71866230105600), ([11,18,18], 36462275136000)]
theorem block021_data : block021 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12235036884000 : Int) atom1536) (SparsePolynomial.scale (10060008291200 : Int) atom1537)) (SparsePolynomial.merge (SparsePolynomial.scale (19067301227520 : Int) atom1538) (SparsePolynomial.merge (SparsePolynomial.scale (30545055374400 : Int) atom1539) (SparsePolynomial.scale (3637196294400 : Int) atom1540)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6880901068800 : Int) atom1541) (SparsePolynomial.scale (8610848568000 : Int) atom1542)) (SparsePolynomial.merge (SparsePolynomial.scale (7226753652000 : Int) atom1543) (SparsePolynomial.merge (SparsePolynomial.scale (24723029116800 : Int) atom1544) (SparsePolynomial.scale (25487556040800 : Int) atom1545))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (29609621330400 : Int) atom1546) (SparsePolynomial.scale (48203677670400 : Int) atom1547)) (SparsePolynomial.merge (SparsePolynomial.scale (7524616377600 : Int) atom1548) (SparsePolynomial.merge (SparsePolynomial.scale (13837762108800 : Int) atom1549) (SparsePolynomial.scale (14444665250400 : Int) atom1550)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39514858588800 : Int) atom1551) (SparsePolynomial.scale (43438294015200 : Int) atom1552)) (SparsePolynomial.merge (SparsePolynomial.scale (44668852452000 : Int) atom1553) (SparsePolynomial.merge (SparsePolynomial.scale (70445302603200 : Int) atom1554) (SparsePolynomial.scale (14207114880000 : Int) atom1555)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31648905514800 : Int) atom1556) (SparsePolynomial.scale (63044385868800 : Int) atom1557)) (SparsePolynomial.merge (SparsePolynomial.scale (68251193312400 : Int) atom1558) (SparsePolynomial.merge (SparsePolynomial.scale (52704630997200 : Int) atom1559) (SparsePolynomial.scale (84534447690000 : Int) atom1560)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13258427535360 : Int) atom1561) (SparsePolynomial.scale (55380479086800 : Int) atom1562)) (SparsePolynomial.merge (SparsePolynomial.scale (67640031660600 : Int) atom1563) (SparsePolynomial.merge (SparsePolynomial.scale (51789484202400 : Int) atom1564) (SparsePolynomial.scale (71505263913300 : Int) atom1565))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (41806301644800 : Int) atom1566) (SparsePolynomial.scale (79803065286000 : Int) atom1567)) (SparsePolynomial.merge (SparsePolynomial.scale (57575234833200 : Int) atom1568) (SparsePolynomial.merge (SparsePolynomial.scale (64172281244400 : Int) atom1569) (SparsePolynomial.scale (32379144373800 : Int) atom1570)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46613159346600 : Int) atom1571) (SparsePolynomial.scale (56384774100900 : Int) atom1572)) (SparsePolynomial.merge (SparsePolynomial.scale (9434482696800 : Int) atom1573) (SparsePolynomial.merge (SparsePolynomial.scale (29846674802700 : Int) atom1574) (SparsePolynomial.scale (16605245065500 : Int) atom1575))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (625628505600 : Int) atom1576) (SparsePolynomial.scale (3027061094400 : Int) atom1577)) (SparsePolynomial.merge (SparsePolynomial.scale (4622441241600 : Int) atom1578) (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1579) (SparsePolynomial.scale (2412192625920 : Int) atom1580)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12512392569600 : Int) atom1581) (SparsePolynomial.scale (6764344227200 : Int) atom1582)) (SparsePolynomial.merge (SparsePolynomial.scale (11598417976320 : Int) atom1583) (SparsePolynomial.merge (SparsePolynomial.scale (17871729019200 : Int) atom1584) (SparsePolynomial.scale (1585379635200 : Int) atom1585))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2686419532800 : Int) atom1586) (SparsePolynomial.scale (2932238030400 : Int) atom1587)) (SparsePolynomial.merge (SparsePolynomial.scale (229178692800 : Int) atom1588) (SparsePolynomial.merge (SparsePolynomial.scale (18882297907200 : Int) atom1589) (SparsePolynomial.scale (16597632038400 : Int) atom1590)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20194842312000 : Int) atom1591) (SparsePolynomial.scale (38617257772800 : Int) atom1592)) (SparsePolynomial.merge (SparsePolynomial.scale (4954771584000 : Int) atom1593) (SparsePolynomial.merge (SparsePolynomial.scale (8093431584000 : Int) atom1594) (SparsePolynomial.scale (8260858368000 : Int) atom1595)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35367383520000 : Int) atom1596) (SparsePolynomial.scale (36765453110400 : Int) atom1597)) (SparsePolynomial.merge (SparsePolynomial.scale (37994983488000 : Int) atom1598) (SparsePolynomial.merge (SparsePolynomial.scale (63945789163200 : Int) atom1599) (SparsePolynomial.scale (11306983564800 : Int) atom1600)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26897818752000 : Int) atom1601) (SparsePolynomial.scale (60580379059200 : Int) atom1602)) (SparsePolynomial.merge (SparsePolynomial.scale (65618034048000 : Int) atom1603) (SparsePolynomial.merge (SparsePolynomial.scale (51049231833600 : Int) atom1604) (SparsePolynomial.scale (83972064960000 : Int) atom1605))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11599244213760 : Int) atom1606) (SparsePolynomial.scale (54517358246400 : Int) atom1607)) (SparsePolynomial.merge (SparsePolynomial.scale (68922680601600 : Int) atom1608) (SparsePolynomial.merge (SparsePolynomial.scale (54987390259200 : Int) atom1609) (SparsePolynomial.scale (76694201740800 : Int) atom1610)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (41556232166400 : Int) atom1611) (SparsePolynomial.scale (83144666304000 : Int) atom1612)) (SparsePolynomial.merge (SparsePolynomial.scale (63150637939200 : Int) atom1613) (SparsePolynomial.merge (SparsePolynomial.scale (71866230105600 : Int) atom1614) (SparsePolynomial.scale (36462275136000 : Int) atom1615)))))))) := by decide +kernel
theorem block021_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block021 := by
  rw [block021_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1536_nonneg g hg hA hB) (atom1537_nonneg g hg hA hB)) (add_nonneg (atom1538_nonneg g hg hA hB) (add_nonneg (atom1539_nonneg g hg hA hB) (atom1540_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1541_nonneg g hg hA hB) (atom1542_nonneg g hg hA hB)) (add_nonneg (atom1543_nonneg g hg hA hB) (add_nonneg (atom1544_nonneg g hg hA hB) (atom1545_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1546_nonneg g hg hA hB) (atom1547_nonneg g hg hA hB)) (add_nonneg (atom1548_nonneg g hg hA hB) (add_nonneg (atom1549_nonneg g hg hA hB) (atom1550_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1551_nonneg g hg hA hB) (atom1552_nonneg g hg hA hB)) (add_nonneg (atom1553_nonneg g hg hA hB) (add_nonneg (atom1554_nonneg g hg hA hB) (atom1555_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1556_nonneg g hg hA hB) (atom1557_nonneg g hg hA hB)) (add_nonneg (atom1558_nonneg g hg hA hB) (add_nonneg (atom1559_nonneg g hg hA hB) (atom1560_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1561_nonneg g hg hA hB) (atom1562_nonneg g hg hA hB)) (add_nonneg (atom1563_nonneg g hg hA hB) (add_nonneg (atom1564_nonneg g hg hA hB) (atom1565_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1566_nonneg g hg hA hB) (atom1567_nonneg g hg hA hB)) (add_nonneg (atom1568_nonneg g hg hA hB) (add_nonneg (atom1569_nonneg g hg hA hB) (atom1570_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1571_nonneg g hg hA hB) (atom1572_nonneg g hg hA hB)) (add_nonneg (atom1573_nonneg g hg hA hB) (add_nonneg (atom1574_nonneg g hg hA hB) (atom1575_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1576_nonneg g hg hA hB) (atom1577_nonneg g hg hA hB)) (add_nonneg (atom1578_nonneg g hg hA hB) (add_nonneg (atom1579_nonneg g hg hA hB) (atom1580_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1581_nonneg g hg hA hB) (atom1582_nonneg g hg hA hB)) (add_nonneg (atom1583_nonneg g hg hA hB) (add_nonneg (atom1584_nonneg g hg hA hB) (atom1585_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1586_nonneg g hg hA hB) (atom1587_nonneg g hg hA hB)) (add_nonneg (atom1588_nonneg g hg hA hB) (add_nonneg (atom1589_nonneg g hg hA hB) (atom1590_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1591_nonneg g hg hA hB) (atom1592_nonneg g hg hA hB)) (add_nonneg (atom1593_nonneg g hg hA hB) (add_nonneg (atom1594_nonneg g hg hA hB) (atom1595_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1596_nonneg g hg hA hB) (atom1597_nonneg g hg hA hB)) (add_nonneg (atom1598_nonneg g hg hA hB) (add_nonneg (atom1599_nonneg g hg hA hB) (atom1600_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1601_nonneg g hg hA hB) (atom1602_nonneg g hg hA hB)) (add_nonneg (atom1603_nonneg g hg hA hB) (add_nonneg (atom1604_nonneg g hg hA hB) (atom1605_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1606_nonneg g hg hA hB) (atom1607_nonneg g hg hA hB)) (add_nonneg (atom1608_nonneg g hg hA hB) (add_nonneg (atom1609_nonneg g hg hA hB) (atom1610_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1611_nonneg g hg hA hB) (atom1612_nonneg g hg hA hB)) (add_nonneg (atom1613_nonneg g hg hA hB) (add_nonneg (atom1614_nonneg g hg hA hB) (atom1615_nonneg g hg hA hB))))))))

end APPT.Finite21
