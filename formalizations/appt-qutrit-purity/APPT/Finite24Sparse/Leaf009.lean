import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0529 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0529 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159710549644800 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0530 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (137694970828800 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0531 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129445179494400 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0532 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121195388160000 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0533 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (124969158917856 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0534 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152006361651936 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0535 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175766709907008 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536 : SparsePolynomial.Poly := [([1,2,12], 1)]
theorem eval_atom0536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0536 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (223360883019648 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537 : SparsePolynomial.Poly := [([1,2,13], 1)]
theorem eval_atom0537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0537 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197788830624000 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538 : SparsePolynomial.Poly := [([1,2,14], 1)]
theorem eval_atom0538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0538 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164868252595200 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539 : SparsePolynomial.Poly := [([1,2,15], 1)]
theorem eval_atom0539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0539 = ((g 1) * (g 2) * (g 15)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (161521687756800 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540 : SparsePolynomial.Poly := [([1,2,16], 1)]
theorem eval_atom0540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0540 = ((g 1) * (g 2) * (g 16)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134530102425600 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541 : SparsePolynomial.Poly := [([1,2,17], 1)]
theorem eval_atom0541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0541 = ((g 1) * (g 2) * (g 17)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (127403994009600 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542 : SparsePolynomial.Poly := [([1,2,18], 1)]
theorem eval_atom0542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0542 = ((g 1) * (g 2) * (g 18)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (179539273267200 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543 : SparsePolynomial.Poly := [([1,2,19], 1)]
theorem eval_atom0543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0543 = ((g 1) * (g 2) * (g 19)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (97636705689600 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544 : SparsePolynomial.Poly := [([1,2,20], 1)]
theorem eval_atom0544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0544 = ((g 1) * (g 2) * (g 20)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163039690598400 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545 : SparsePolynomial.Poly := [([1,2,21], 1)]
theorem eval_atom0545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0545 = ((g 1) * (g 2) * (g 21)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88734868992000 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546 : SparsePolynomial.Poly := [([1,2,22], 1)]
theorem eval_atom0546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0546 = ((g 1) * (g 2) * (g 22)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62854509849600 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 2) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547 : SparsePolynomial.Poly := [([1,2,23], 1)]
theorem eval_atom0547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0547 = ((g 1) * (g 2) * (g 23)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56808566337600 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 2) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0548 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70931195596800 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0549 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135653785344000 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0550 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (143210966976000 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0551 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (123236573644800 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0552 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (117027967795200 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0553 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110819361945600 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0554 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116634318188256 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0555 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145712706407136 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0556 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171514240147008 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557 : SparsePolynomial.Poly := [([1,3,12], 1)]
theorem eval_atom0557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0557 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221149598744448 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558 : SparsePolynomial.Poly := [([1,3,13], 1)]
theorem eval_atom0558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0558 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197618731833600 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559 : SparsePolynomial.Poly := [([1,3,14], 1)]
theorem eval_atom0559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0559 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166739339289600 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560 : SparsePolynomial.Poly := [([1,3,15], 1)]
theorem eval_atom0560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0560 = ((g 1) * (g 3) * (g 15)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165433959936000 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561 : SparsePolynomial.Poly := [([1,3,16], 1)]
theorem eval_atom0561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0561 = ((g 1) * (g 3) * (g 16)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140483560089600 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562 : SparsePolynomial.Poly := [([1,3,17], 1)]
theorem eval_atom0562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0562 = ((g 1) * (g 3) * (g 17)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135398637158400 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563 : SparsePolynomial.Poly := [([1,3,18], 1)]
theorem eval_atom0563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0563 = ((g 1) * (g 3) * (g 18)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189575101900800 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564 : SparsePolynomial.Poly := [([1,3,19], 1)]
theorem eval_atom0564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0564 = ((g 1) * (g 3) * (g 19)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (123661820620800 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565 : SparsePolynomial.Poly := [([1,3,20], 1)]
theorem eval_atom0565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0565 = ((g 1) * (g 3) * (g 20)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177157890201600 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566 : SparsePolynomial.Poly := [([1,3,21], 1)]
theorem eval_atom0566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0566 = ((g 1) * (g 3) * (g 21)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125050960742400 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567 : SparsePolynomial.Poly := [([1,3,22], 1)]
theorem eval_atom0567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0567 = ((g 1) * (g 3) * (g 22)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (119748045043200 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568 : SparsePolynomial.Poly := [([1,3,23], 1)]
theorem eval_atom0568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0568 = ((g 1) * (g 3) * (g 23)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (85276193587200 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0569 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71527991068800 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0570 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (131094501748848 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0571 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108778176460800 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0572 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104610756096000 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0573 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100443335731200 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574 : SparsePolynomial.Poly := [([1,4,9], 1)]
theorem eval_atom0574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0574 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108299477458656 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575 : SparsePolynomial.Poly := [([1,4,10], 1)]
theorem eval_atom0575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0575 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (139419051162336 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576 : SparsePolynomial.Poly := [([1,4,11], 1)]
theorem eval_atom0576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0576 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (167261770387008 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577 : SparsePolynomial.Poly := [([1,4,12], 1)]
theorem eval_atom0577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0577 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (218938314469248 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578 : SparsePolynomial.Poly := [([1,4,13], 1)]
theorem eval_atom0578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0578 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197448633043200 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579 : SparsePolynomial.Poly := [([1,4,14], 1)]
theorem eval_atom0579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0579 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (168610425984000 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580 : SparsePolynomial.Poly := [([1,4,15], 1)]
theorem eval_atom0580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0580 = ((g 1) * (g 4) * (g 15)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (169346232115200 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581 : SparsePolynomial.Poly := [([1,4,16], 1)]
theorem eval_atom0581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0581 = ((g 1) * (g 4) * (g 16)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146437017753600 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582 : SparsePolynomial.Poly := [([1,4,17], 1)]
theorem eval_atom0582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0582 = ((g 1) * (g 4) * (g 17)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145716997305600 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583 : SparsePolynomial.Poly := [([1,4,18], 1)]
theorem eval_atom0583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0583 = ((g 1) * (g 4) * (g 18)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (199610930534400 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584 : SparsePolynomial.Poly := [([1,4,19], 1)]
theorem eval_atom0584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0584 = ((g 1) * (g 4) * (g 19)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152680778964000 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585 : SparsePolynomial.Poly := [([1,4,20], 1)]
theorem eval_atom0585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0585 = ((g 1) * (g 4) * (g 20)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (191722236703200 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586 : SparsePolynomial.Poly := [([1,4,21], 1)]
theorem eval_atom0586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0586 = ((g 1) * (g 4) * (g 21)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163638700898400 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587 : SparsePolynomial.Poly := [([1,4,22], 1)]
theorem eval_atom0587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0587 = ((g 1) * (g 4) * (g 22)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (184533468789600 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588 : SparsePolynomial.Poly := [([1,4,23], 1)]
theorem eval_atom0588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0588 = ((g 1) * (g 4) * (g 23)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135594629301600 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0589 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88198484774400 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0590 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134283854068848 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0591 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121414226836848 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0592 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120824747371152 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593 : SparsePolynomial.Poly := [([1,5,9], 1)]
theorem eval_atom0593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0593 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (128906875593144 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594 : SparsePolynomial.Poly := [([1,5,10], 1)]
theorem eval_atom0594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0594 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (151977742829352 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595 : SparsePolynomial.Poly := [([1,5,11], 1)]
theorem eval_atom0595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0595 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (176775088108608 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596 : SparsePolynomial.Poly := [([1,5,12], 1)]
theorem eval_atom0596 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0596 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0596_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230492817675648 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597 : SparsePolynomial.Poly := [([1,5,13], 1)]
theorem eval_atom0597 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0597 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0597_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211044321734400 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598 : SparsePolynomial.Poly := [([1,5,14], 1)]
theorem eval_atom0598 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0598 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0598_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (184247300160000 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599 : SparsePolynomial.Poly := [([1,5,15], 1)]
theorem eval_atom0599 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0599 = ((g 1) * (g 5) * (g 15)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0599_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (187393161312000 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600 : SparsePolynomial.Poly := [([1,5,16], 1)]
theorem eval_atom0600 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0600 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0600_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (172805257094400 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601 : SparsePolynomial.Poly := [([1,5,17], 1)]
theorem eval_atom0601 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0601 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0601_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (173116460563200 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602 : SparsePolynomial.Poly := [([1,5,18], 1)]
theorem eval_atom0602 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0602 = ((g 1) * (g 5) * (g 18)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0602_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (223412546649600 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603 : SparsePolynomial.Poly := [([1,5,19], 1)]
theorem eval_atom0603 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0603 = ((g 1) * (g 5) * (g 19)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0603_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (185452241990400 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604 : SparsePolynomial.Poly := [([1,5,20], 1)]
theorem eval_atom0604 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0604 = ((g 1) * (g 5) * (g 20)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0604_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (227731291603200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605 : SparsePolynomial.Poly := [([1,5,21], 1)]
theorem eval_atom0605 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0605 = ((g 1) * (g 5) * (g 21)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0605_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205091715628800 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606 : SparsePolynomial.Poly := [([1,5,22], 1)]
theorem eval_atom0606 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0606 = ((g 1) * (g 5) * (g 22)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0606_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238961209267200 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607 : SparsePolynomial.Poly := [([1,5,23], 1)]
theorem eval_atom0607 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0607 = ((g 1) * (g 5) * (g 23)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0607_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221088695990400 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0608 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0608 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0608_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89684587238400 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block009 : SparsePolynomial.Poly := [([1,2,5], 159710549644800), ([1,2,6], 137694970828800), ([1,2,7], 129445179494400), ([1,2,8], 121195388160000), ([1,2,9], 124969158917856), ([1,2,10], 152006361651936), ([1,2,11], 175766709907008), ([1,2,12], 223360883019648), ([1,2,13], 197788830624000), ([1,2,14], 164868252595200), ([1,2,15], 161521687756800), ([1,2,16], 134530102425600), ([1,2,17], 127403994009600), ([1,2,18], 179539273267200), ([1,2,19], 97636705689600), ([1,2,20], 163039690598400), ([1,2,21], 88734868992000), ([1,2,22], 62854509849600), ([1,2,23], 56808566337600), ([1,3,3], 70931195596800), ([1,3,4], 135653785344000), ([1,3,5], 143210966976000), ([1,3,6], 123236573644800), ([1,3,7], 117027967795200), ([1,3,8], 110819361945600), ([1,3,9], 116634318188256), ([1,3,10], 145712706407136), ([1,3,11], 171514240147008), ([1,3,12], 221149598744448), ([1,3,13], 197618731833600), ([1,3,14], 166739339289600), ([1,3,15], 165433959936000), ([1,3,16], 140483560089600), ([1,3,17], 135398637158400), ([1,3,18], 189575101900800), ([1,3,19], 123661820620800), ([1,3,20], 177157890201600), ([1,3,21], 125050960742400), ([1,3,22], 119748045043200), ([1,3,23], 85276193587200), ([1,4,4], 71527991068800), ([1,4,5], 131094501748848), ([1,4,6], 108778176460800), ([1,4,7], 104610756096000), ([1,4,8], 100443335731200), ([1,4,9], 108299477458656), ([1,4,10], 139419051162336), ([1,4,11], 167261770387008), ([1,4,12], 218938314469248), ([1,4,13], 197448633043200), ([1,4,14], 168610425984000), ([1,4,15], 169346232115200), ([1,4,16], 146437017753600), ([1,4,17], 145716997305600), ([1,4,18], 199610930534400), ([1,4,19], 152680778964000), ([1,4,20], 191722236703200), ([1,4,21], 163638700898400), ([1,4,22], 184533468789600), ([1,4,23], 135594629301600), ([1,5,5], 88198484774400), ([1,5,6], 134283854068848), ([1,5,7], 121414226836848), ([1,5,8], 120824747371152), ([1,5,9], 128906875593144), ([1,5,10], 151977742829352), ([1,5,11], 176775088108608), ([1,5,12], 230492817675648), ([1,5,13], 211044321734400), ([1,5,14], 184247300160000), ([1,5,15], 187393161312000), ([1,5,16], 172805257094400), ([1,5,17], 173116460563200), ([1,5,18], 223412546649600), ([1,5,19], 185452241990400), ([1,5,20], 227731291603200), ([1,5,21], 205091715628800), ([1,5,22], 238961209267200), ([1,5,23], 221088695990400), ([1,6,6], 89684587238400)]
theorem block009_data : block009 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (159710549644800 : Int) atom0529) (SparsePolynomial.scale (137694970828800 : Int) atom0530)) (SparsePolynomial.merge (SparsePolynomial.scale (129445179494400 : Int) atom0531) (SparsePolynomial.merge (SparsePolynomial.scale (121195388160000 : Int) atom0532) (SparsePolynomial.scale (124969158917856 : Int) atom0533)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (152006361651936 : Int) atom0534) (SparsePolynomial.scale (175766709907008 : Int) atom0535)) (SparsePolynomial.merge (SparsePolynomial.scale (223360883019648 : Int) atom0536) (SparsePolynomial.merge (SparsePolynomial.scale (197788830624000 : Int) atom0537) (SparsePolynomial.scale (164868252595200 : Int) atom0538))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (161521687756800 : Int) atom0539) (SparsePolynomial.scale (134530102425600 : Int) atom0540)) (SparsePolynomial.merge (SparsePolynomial.scale (127403994009600 : Int) atom0541) (SparsePolynomial.merge (SparsePolynomial.scale (179539273267200 : Int) atom0542) (SparsePolynomial.scale (97636705689600 : Int) atom0543)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (163039690598400 : Int) atom0544) (SparsePolynomial.scale (88734868992000 : Int) atom0545)) (SparsePolynomial.merge (SparsePolynomial.scale (62854509849600 : Int) atom0546) (SparsePolynomial.merge (SparsePolynomial.scale (56808566337600 : Int) atom0547) (SparsePolynomial.scale (70931195596800 : Int) atom0548)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (135653785344000 : Int) atom0549) (SparsePolynomial.scale (143210966976000 : Int) atom0550)) (SparsePolynomial.merge (SparsePolynomial.scale (123236573644800 : Int) atom0551) (SparsePolynomial.merge (SparsePolynomial.scale (117027967795200 : Int) atom0552) (SparsePolynomial.scale (110819361945600 : Int) atom0553)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (116634318188256 : Int) atom0554) (SparsePolynomial.scale (145712706407136 : Int) atom0555)) (SparsePolynomial.merge (SparsePolynomial.scale (171514240147008 : Int) atom0556) (SparsePolynomial.merge (SparsePolynomial.scale (221149598744448 : Int) atom0557) (SparsePolynomial.scale (197618731833600 : Int) atom0558))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (166739339289600 : Int) atom0559) (SparsePolynomial.scale (165433959936000 : Int) atom0560)) (SparsePolynomial.merge (SparsePolynomial.scale (140483560089600 : Int) atom0561) (SparsePolynomial.merge (SparsePolynomial.scale (135398637158400 : Int) atom0562) (SparsePolynomial.scale (189575101900800 : Int) atom0563)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (123661820620800 : Int) atom0564) (SparsePolynomial.scale (177157890201600 : Int) atom0565)) (SparsePolynomial.merge (SparsePolynomial.scale (125050960742400 : Int) atom0566) (SparsePolynomial.merge (SparsePolynomial.scale (119748045043200 : Int) atom0567) (SparsePolynomial.scale (85276193587200 : Int) atom0568))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (71527991068800 : Int) atom0569) (SparsePolynomial.scale (131094501748848 : Int) atom0570)) (SparsePolynomial.merge (SparsePolynomial.scale (108778176460800 : Int) atom0571) (SparsePolynomial.merge (SparsePolynomial.scale (104610756096000 : Int) atom0572) (SparsePolynomial.scale (100443335731200 : Int) atom0573)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (108299477458656 : Int) atom0574) (SparsePolynomial.scale (139419051162336 : Int) atom0575)) (SparsePolynomial.merge (SparsePolynomial.scale (167261770387008 : Int) atom0576) (SparsePolynomial.merge (SparsePolynomial.scale (218938314469248 : Int) atom0577) (SparsePolynomial.scale (197448633043200 : Int) atom0578))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (168610425984000 : Int) atom0579) (SparsePolynomial.scale (169346232115200 : Int) atom0580)) (SparsePolynomial.merge (SparsePolynomial.scale (146437017753600 : Int) atom0581) (SparsePolynomial.merge (SparsePolynomial.scale (145716997305600 : Int) atom0582) (SparsePolynomial.scale (199610930534400 : Int) atom0583)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (152680778964000 : Int) atom0584) (SparsePolynomial.scale (191722236703200 : Int) atom0585)) (SparsePolynomial.merge (SparsePolynomial.scale (163638700898400 : Int) atom0586) (SparsePolynomial.merge (SparsePolynomial.scale (184533468789600 : Int) atom0587) (SparsePolynomial.scale (135594629301600 : Int) atom0588)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88198484774400 : Int) atom0589) (SparsePolynomial.scale (134283854068848 : Int) atom0590)) (SparsePolynomial.merge (SparsePolynomial.scale (121414226836848 : Int) atom0591) (SparsePolynomial.merge (SparsePolynomial.scale (120824747371152 : Int) atom0592) (SparsePolynomial.scale (128906875593144 : Int) atom0593)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (151977742829352 : Int) atom0594) (SparsePolynomial.scale (176775088108608 : Int) atom0595)) (SparsePolynomial.merge (SparsePolynomial.scale (230492817675648 : Int) atom0596) (SparsePolynomial.merge (SparsePolynomial.scale (211044321734400 : Int) atom0597) (SparsePolynomial.scale (184247300160000 : Int) atom0598))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (187393161312000 : Int) atom0599) (SparsePolynomial.scale (172805257094400 : Int) atom0600)) (SparsePolynomial.merge (SparsePolynomial.scale (173116460563200 : Int) atom0601) (SparsePolynomial.merge (SparsePolynomial.scale (223412546649600 : Int) atom0602) (SparsePolynomial.scale (185452241990400 : Int) atom0603)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (227731291603200 : Int) atom0604) (SparsePolynomial.scale (205091715628800 : Int) atom0605)) (SparsePolynomial.merge (SparsePolynomial.scale (238961209267200 : Int) atom0606) (SparsePolynomial.merge (SparsePolynomial.scale (221088695990400 : Int) atom0607) (SparsePolynomial.scale (89684587238400 : Int) atom0608)))))))) := by decide +kernel
theorem block009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block009 := by
  rw [block009_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0529_nonneg g hg hA hB) (atom0530_nonneg g hg hA hB)) (add_nonneg (atom0531_nonneg g hg hA hB) (add_nonneg (atom0532_nonneg g hg hA hB) (atom0533_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0534_nonneg g hg hA hB) (atom0535_nonneg g hg hA hB)) (add_nonneg (atom0536_nonneg g hg hA hB) (add_nonneg (atom0537_nonneg g hg hA hB) (atom0538_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0539_nonneg g hg hA hB) (atom0540_nonneg g hg hA hB)) (add_nonneg (atom0541_nonneg g hg hA hB) (add_nonneg (atom0542_nonneg g hg hA hB) (atom0543_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0544_nonneg g hg hA hB) (atom0545_nonneg g hg hA hB)) (add_nonneg (atom0546_nonneg g hg hA hB) (add_nonneg (atom0547_nonneg g hg hA hB) (atom0548_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0549_nonneg g hg hA hB) (atom0550_nonneg g hg hA hB)) (add_nonneg (atom0551_nonneg g hg hA hB) (add_nonneg (atom0552_nonneg g hg hA hB) (atom0553_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0554_nonneg g hg hA hB) (atom0555_nonneg g hg hA hB)) (add_nonneg (atom0556_nonneg g hg hA hB) (add_nonneg (atom0557_nonneg g hg hA hB) (atom0558_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0559_nonneg g hg hA hB) (atom0560_nonneg g hg hA hB)) (add_nonneg (atom0561_nonneg g hg hA hB) (add_nonneg (atom0562_nonneg g hg hA hB) (atom0563_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0564_nonneg g hg hA hB) (atom0565_nonneg g hg hA hB)) (add_nonneg (atom0566_nonneg g hg hA hB) (add_nonneg (atom0567_nonneg g hg hA hB) (atom0568_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0569_nonneg g hg hA hB) (atom0570_nonneg g hg hA hB)) (add_nonneg (atom0571_nonneg g hg hA hB) (add_nonneg (atom0572_nonneg g hg hA hB) (atom0573_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0574_nonneg g hg hA hB) (atom0575_nonneg g hg hA hB)) (add_nonneg (atom0576_nonneg g hg hA hB) (add_nonneg (atom0577_nonneg g hg hA hB) (atom0578_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0579_nonneg g hg hA hB) (atom0580_nonneg g hg hA hB)) (add_nonneg (atom0581_nonneg g hg hA hB) (add_nonneg (atom0582_nonneg g hg hA hB) (atom0583_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0584_nonneg g hg hA hB) (atom0585_nonneg g hg hA hB)) (add_nonneg (atom0586_nonneg g hg hA hB) (add_nonneg (atom0587_nonneg g hg hA hB) (atom0588_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0589_nonneg g hg hA hB) (atom0590_nonneg g hg hA hB)) (add_nonneg (atom0591_nonneg g hg hA hB) (add_nonneg (atom0592_nonneg g hg hA hB) (atom0593_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0594_nonneg g hg hA hB) (atom0595_nonneg g hg hA hB)) (add_nonneg (atom0596_nonneg g hg hA hB) (add_nonneg (atom0597_nonneg g hg hA hB) (atom0598_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0599_nonneg g hg hA hB) (atom0600_nonneg g hg hA hB)) (add_nonneg (atom0601_nonneg g hg hA hB) (add_nonneg (atom0602_nonneg g hg hA hB) (atom0603_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0604_nonneg g hg hA hB) (atom0605_nonneg g hg hA hB)) (add_nonneg (atom0606_nonneg g hg hA hB) (add_nonneg (atom0607_nonneg g hg hA hB) (atom0608_nonneg g hg hA hB))))))))

end APPT.Finite24
