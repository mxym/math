import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2529 : SparsePolynomial.Poly := [([17,19,21], 1)]
theorem eval_atom2529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2529 = ((g 17) * (g 19) * (g 21)) := by
  norm_num [atom2529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (636169476096000 : Int) atom2529) := by
  rw [SparsePolynomial.eval_scale, eval_atom2529]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2530 : SparsePolynomial.Poly := [([17,19,22], 1)]
theorem eval_atom2530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2530 = ((g 17) * (g 19) * (g 22)) := by
  norm_num [atom2530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (597975854515200 : Int) atom2530) := by
  rw [SparsePolynomial.eval_scale, eval_atom2530]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2531 : SparsePolynomial.Poly := [([17,19,23], 1)]
theorem eval_atom2531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2531 = ((g 17) * (g 19) * (g 23)) := by
  norm_num [atom2531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (820556564889600 : Int) atom2531) := by
  rw [SparsePolynomial.eval_scale, eval_atom2531]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2532 : SparsePolynomial.Poly := [([17,20,20], 1)]
theorem eval_atom2532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2532 = ((g 17) * (g 20) * (g 20)) := by
  norm_num [atom2532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (368221356518400 : Int) atom2532) := by
  rw [SparsePolynomial.eval_scale, eval_atom2532]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2533 : SparsePolynomial.Poly := [([17,20,21], 1)]
theorem eval_atom2533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2533 = ((g 17) * (g 20) * (g 21)) := by
  norm_num [atom2533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (781603941888000 : Int) atom2533) := by
  rw [SparsePolynomial.eval_scale, eval_atom2533]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2534 : SparsePolynomial.Poly := [([17,20,22], 1)]
theorem eval_atom2534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2534 = ((g 17) * (g 20) * (g 22)) := by
  norm_num [atom2534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (761659858713600 : Int) atom2534) := by
  rw [SparsePolynomial.eval_scale, eval_atom2534]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2535 : SparsePolynomial.Poly := [([17,20,23], 1)]
theorem eval_atom2535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2535 = ((g 17) * (g 20) * (g 23)) := by
  norm_num [atom2535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (841818913689600 : Int) atom2535) := by
  rw [SparsePolynomial.eval_scale, eval_atom2535]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2536 : SparsePolynomial.Poly := [([17,21,21], 1)]
theorem eval_atom2536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2536 = ((g 17) * (g 21) * (g 21)) := by
  norm_num [atom2536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (357887855001600 : Int) atom2536) := by
  rw [SparsePolynomial.eval_scale, eval_atom2536]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2537 : SparsePolynomial.Poly := [([17,21,22], 1)]
theorem eval_atom2537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2537 = ((g 17) * (g 21) * (g 22)) := by
  norm_num [atom2537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (784623195417600 : Int) atom2537) := by
  rw [SparsePolynomial.eval_scale, eval_atom2537]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2538 : SparsePolynomial.Poly := [([17,21,23], 1)]
theorem eval_atom2538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2538 = ((g 17) * (g 21) * (g 23)) := by
  norm_num [atom2538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (883152919756800 : Int) atom2538) := by
  rw [SparsePolynomial.eval_scale, eval_atom2538]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2539 : SparsePolynomial.Poly := [([17,22,22], 1)]
theorem eval_atom2539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2539 = ((g 17) * (g 22) * (g 22)) := by
  norm_num [atom2539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397355445648000 : Int) atom2539) := by
  rw [SparsePolynomial.eval_scale, eval_atom2539]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2540 : SparsePolynomial.Poly := [([17,22,23], 1)]
theorem eval_atom2540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2540 = ((g 17) * (g 22) * (g 23)) := by
  norm_num [atom2540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924486925824000 : Int) atom2540) := by
  rw [SparsePolynomial.eval_scale, eval_atom2540]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2541 : SparsePolynomial.Poly := [([17,23,23], 1)]
theorem eval_atom2541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2541 = ((g 17) * (g 23) * (g 23)) := by
  norm_num [atom2541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472874637312000 : Int) atom2541) := by
  rw [SparsePolynomial.eval_scale, eval_atom2541]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2542 : SparsePolynomial.Poly := [([18,18,18], 1)]
theorem eval_atom2542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2542 = ((g 18) * (g 18) * (g 18)) := by
  norm_num [atom2542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10354763865600 : Int) atom2542) := by
  rw [SparsePolynomial.eval_scale, eval_atom2542]
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 18) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2543 : SparsePolynomial.Poly := [([18,18,19], 1)]
theorem eval_atom2543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2543 = ((g 18) * (g 18) * (g 19)) := by
  norm_num [atom2543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76586980377600 : Int) atom2543) := by
  rw [SparsePolynomial.eval_scale, eval_atom2543]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2544 : SparsePolynomial.Poly := [([18,18,20], 1)]
theorem eval_atom2544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2544 = ((g 18) * (g 18) * (g 20)) := by
  norm_num [atom2544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262951467609600 : Int) atom2544) := by
  rw [SparsePolynomial.eval_scale, eval_atom2544]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2545 : SparsePolynomial.Poly := [([18,18,21], 1)]
theorem eval_atom2545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2545 = ((g 18) * (g 18) * (g 21)) := by
  norm_num [atom2545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308474156390400 : Int) atom2545) := by
  rw [SparsePolynomial.eval_scale, eval_atom2545]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2546 : SparsePolynomial.Poly := [([18,18,22], 1)]
theorem eval_atom2546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2546 = ((g 18) * (g 18) * (g 22)) := by
  norm_num [atom2546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220891320115200 : Int) atom2546) := by
  rw [SparsePolynomial.eval_scale, eval_atom2546]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2547 : SparsePolynomial.Poly := [([18,18,23], 1)]
theorem eval_atom2547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2547 = ((g 18) * (g 18) * (g 23)) := by
  norm_num [atom2547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399519533952000 : Int) atom2547) := by
  rw [SparsePolynomial.eval_scale, eval_atom2547]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2548 : SparsePolynomial.Poly := [([18,19,19], 1)]
theorem eval_atom2548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2548 = ((g 18) * (g 19) * (g 19)) := by
  norm_num [atom2548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72104877250560 : Int) atom2548) := by
  rw [SparsePolynomial.eval_scale, eval_atom2548]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2549 : SparsePolynomial.Poly := [([18,19,20], 1)]
theorem eval_atom2549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2549 = ((g 18) * (g 19) * (g 20)) := by
  norm_num [atom2549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519184032998400 : Int) atom2549) := by
  rw [SparsePolynomial.eval_scale, eval_atom2549]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2550 : SparsePolynomial.Poly := [([18,19,21], 1)]
theorem eval_atom2550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2550 = ((g 18) * (g 19) * (g 21)) := by
  norm_num [atom2550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (700041571891200 : Int) atom2550) := by
  rw [SparsePolynomial.eval_scale, eval_atom2550]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2551 : SparsePolynomial.Poly := [([18,19,22], 1)]
theorem eval_atom2551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2551 = ((g 18) * (g 19) * (g 22)) := by
  norm_num [atom2551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (614688060672000 : Int) atom2551) := by
  rw [SparsePolynomial.eval_scale, eval_atom2551]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2552 : SparsePolynomial.Poly := [([18,19,23], 1)]
theorem eval_atom2552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2552 = ((g 18) * (g 19) * (g 23)) := by
  norm_num [atom2552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (850493952000000 : Int) atom2552) := by
  rw [SparsePolynomial.eval_scale, eval_atom2552]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2553 : SparsePolynomial.Poly := [([18,20,20], 1)]
theorem eval_atom2553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2553 = ((g 18) * (g 20) * (g 20)) := by
  norm_num [atom2553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397074363840000 : Int) atom2553) := by
  rw [SparsePolynomial.eval_scale, eval_atom2553]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2554 : SparsePolynomial.Poly := [([18,20,21], 1)]
theorem eval_atom2554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2554 = ((g 18) * (g 20) * (g 21)) := by
  norm_num [atom2554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853555730227200 : Int) atom2554) := by
  rw [SparsePolynomial.eval_scale, eval_atom2554]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2555 : SparsePolynomial.Poly := [([18,20,22], 1)]
theorem eval_atom2555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2555 = ((g 18) * (g 20) * (g 22)) := by
  norm_num [atom2555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (787472350156800 : Int) atom2555) := by
  rw [SparsePolynomial.eval_scale, eval_atom2555]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2556 : SparsePolynomial.Poly := [([18,20,23], 1)]
theorem eval_atom2556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2556 = ((g 18) * (g 20) * (g 23)) := by
  norm_num [atom2556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (761107037644800 : Int) atom2556) := by
  rw [SparsePolynomial.eval_scale, eval_atom2556]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2557 : SparsePolynomial.Poly := [([18,21,21], 1)]
theorem eval_atom2557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2557 = ((g 18) * (g 21) * (g 21)) := by
  norm_num [atom2557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397903595443200 : Int) atom2557) := by
  rw [SparsePolynomial.eval_scale, eval_atom2557]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2558 : SparsePolynomial.Poly := [([18,21,22], 1)]
theorem eval_atom2558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2558 = ((g 18) * (g 21) * (g 22)) := by
  norm_num [atom2558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (819535972147200 : Int) atom2558) := by
  rw [SparsePolynomial.eval_scale, eval_atom2558]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2559 : SparsePolynomial.Poly := [([18,21,23], 1)]
theorem eval_atom2559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2559 = ((g 18) * (g 21) * (g 23)) := by
  norm_num [atom2559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (812561921740800 : Int) atom2559) := by
  rw [SparsePolynomial.eval_scale, eval_atom2559]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2560 : SparsePolynomial.Poly := [([18,22,22], 1)]
theorem eval_atom2560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2560 = ((g 18) * (g 22) * (g 22)) := by
  norm_num [atom2560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (418743032904000 : Int) atom2560) := by
  rw [SparsePolynomial.eval_scale, eval_atom2560]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2561 : SparsePolynomial.Poly := [([18,22,23], 1)]
theorem eval_atom2561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2561 = ((g 18) * (g 22) * (g 23)) := by
  norm_num [atom2561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (863774543923200 : Int) atom2561) := by
  rw [SparsePolynomial.eval_scale, eval_atom2561]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2562 : SparsePolynomial.Poly := [([18,23,23], 1)]
theorem eval_atom2562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2562 = ((g 18) * (g 23) * (g 23)) := by
  norm_num [atom2562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (387314945740800 : Int) atom2562) := by
  rw [SparsePolynomial.eval_scale, eval_atom2562]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2563 : SparsePolynomial.Poly := [([19,19,20], 1)]
theorem eval_atom2563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2563 = ((g 19) * (g 19) * (g 20)) := by
  norm_num [atom2563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185526750689280 : Int) atom2563) := by
  rw [SparsePolynomial.eval_scale, eval_atom2563]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2564 : SparsePolynomial.Poly := [([19,19,21], 1)]
theorem eval_atom2564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2564 = ((g 19) * (g 19) * (g 21)) := by
  norm_num [atom2564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315329137643520 : Int) atom2564) := by
  rw [SparsePolynomial.eval_scale, eval_atom2564]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2565 : SparsePolynomial.Poly := [([19,19,22], 1)]
theorem eval_atom2565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2565 = ((g 19) * (g 19) * (g 22)) := by
  norm_num [atom2565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309576576960000 : Int) atom2565) := by
  rw [SparsePolynomial.eval_scale, eval_atom2565]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2566 : SparsePolynomial.Poly := [([19,19,23], 1)]
theorem eval_atom2566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2566 = ((g 19) * (g 19) * (g 23)) := by
  norm_num [atom2566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (429193267937280 : Int) atom2566) := by
  rw [SparsePolynomial.eval_scale, eval_atom2566]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2567 : SparsePolynomial.Poly := [([19,20,20], 1)]
theorem eval_atom2567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2567 = ((g 19) * (g 20) * (g 20)) := by
  norm_num [atom2567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (325313936640000 : Int) atom2567) := by
  rw [SparsePolynomial.eval_scale, eval_atom2567]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2568 : SparsePolynomial.Poly := [([19,20,21], 1)]
theorem eval_atom2568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2568 = ((g 19) * (g 20) * (g 21)) := by
  norm_num [atom2568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (794701548748800 : Int) atom2568) := by
  rw [SparsePolynomial.eval_scale, eval_atom2568]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2569 : SparsePolynomial.Poly := [([19,20,22], 1)]
theorem eval_atom2569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2569 = ((g 19) * (g 20) * (g 22)) := by
  norm_num [atom2569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (813284841600000 : Int) atom2569) := by
  rw [SparsePolynomial.eval_scale, eval_atom2569]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2570 : SparsePolynomial.Poly := [([19,20,23], 1)]
theorem eval_atom2570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2570 = ((g 19) * (g 20) * (g 23)) := by
  norm_num [atom2570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (801165302784000 : Int) atom2570) := by
  rw [SparsePolynomial.eval_scale, eval_atom2570]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2571 : SparsePolynomial.Poly := [([19,21,21], 1)]
theorem eval_atom2571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2571 = ((g 19) * (g 21) * (g 21)) := by
  norm_num [atom2571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407726800588800 : Int) atom2571) := by
  rw [SparsePolynomial.eval_scale, eval_atom2571]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2572 : SparsePolynomial.Poly := [([19,21,22], 1)]
theorem eval_atom2572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2572 = ((g 19) * (g 21) * (g 22)) := by
  norm_num [atom2572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854448748876800 : Int) atom2572) := by
  rw [SparsePolynomial.eval_scale, eval_atom2572]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2573 : SparsePolynomial.Poly := [([19,21,23], 1)]
theorem eval_atom2573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2573 = ((g 19) * (g 21) * (g 23)) := by
  norm_num [atom2573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (862741064908800 : Int) atom2573) := by
  rw [SparsePolynomial.eval_scale, eval_atom2573]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2574 : SparsePolynomial.Poly := [([19,22,22], 1)]
theorem eval_atom2574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2574 = ((g 19) * (g 22) * (g 22)) := by
  norm_num [atom2574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440130620160000 : Int) atom2574) := by
  rw [SparsePolynomial.eval_scale, eval_atom2574]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2575 : SparsePolynomial.Poly := [([19,22,23], 1)]
theorem eval_atom2575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2575 = ((g 19) * (g 22) * (g 23)) := by
  norm_num [atom2575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924074565120000 : Int) atom2575) := by
  rw [SparsePolynomial.eval_scale, eval_atom2575]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2576 : SparsePolynomial.Poly := [([19,23,23], 1)]
theorem eval_atom2576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2576 = ((g 19) * (g 23) * (g 23)) := by
  norm_num [atom2576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422525395353600 : Int) atom2576) := by
  rw [SparsePolynomial.eval_scale, eval_atom2576]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2577 : SparsePolynomial.Poly := [([20,20,20], 1)]
theorem eval_atom2577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2577 = ((g 20) * (g 20) * (g 20)) := by
  norm_num [atom2577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131465102630400 : Int) atom2577) := by
  rw [SparsePolynomial.eval_scale, eval_atom2577]
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 20) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2578 : SparsePolynomial.Poly := [([20,20,21], 1)]
theorem eval_atom2578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2578 = ((g 20) * (g 20) * (g 21)) := by
  norm_num [atom2578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403134133248000 : Int) atom2578) := by
  rw [SparsePolynomial.eval_scale, eval_atom2578]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 20) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2579 : SparsePolynomial.Poly := [([20,20,22], 1)]
theorem eval_atom2579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2579 = ((g 20) * (g 20) * (g 22)) := by
  norm_num [atom2579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419548666521600 : Int) atom2579) := by
  rw [SparsePolynomial.eval_scale, eval_atom2579]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2580 : SparsePolynomial.Poly := [([20,20,23], 1)]
theorem eval_atom2580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2580 = ((g 20) * (g 20) * (g 23)) := by
  norm_num [atom2580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279769985510400 : Int) atom2580) := by
  rw [SparsePolynomial.eval_scale, eval_atom2580]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2581 : SparsePolynomial.Poly := [([20,21,21], 1)]
theorem eval_atom2581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2581 = ((g 20) * (g 21) * (g 21)) := by
  norm_num [atom2581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417550005734400 : Int) atom2581) := by
  rw [SparsePolynomial.eval_scale, eval_atom2581]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 20) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2582 : SparsePolynomial.Poly := [([20,21,22], 1)]
theorem eval_atom2582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2582 = ((g 20) * (g 21) * (g 22)) := by
  norm_num [atom2582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (889361525606400 : Int) atom2582) := by
  rw [SparsePolynomial.eval_scale, eval_atom2582]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2583 : SparsePolynomial.Poly := [([20,21,23], 1)]
theorem eval_atom2583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2583 = ((g 20) * (g 21) * (g 23)) := by
  norm_num [atom2583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (631236611174400 : Int) atom2583) := by
  rw [SparsePolynomial.eval_scale, eval_atom2583]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2584 : SparsePolynomial.Poly := [([20,22,22], 1)]
theorem eval_atom2584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2584 = ((g 20) * (g 22) * (g 22)) := by
  norm_num [atom2584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461518207416000 : Int) atom2584) := by
  rw [SparsePolynomial.eval_scale, eval_atom2584]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2585 : SparsePolynomial.Poly := [([20,22,23], 1)]
theorem eval_atom2585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2585 = ((g 20) * (g 22) * (g 23)) := by
  norm_num [atom2585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (671988157747200 : Int) atom2585) := by
  rw [SparsePolynomial.eval_scale, eval_atom2585]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2586 : SparsePolynomial.Poly := [([20,23,23], 1)]
theorem eval_atom2586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2586 = ((g 20) * (g 23) * (g 23)) := by
  norm_num [atom2586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176052248064000 : Int) atom2586) := by
  rw [SparsePolynomial.eval_scale, eval_atom2586]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2587 : SparsePolynomial.Poly := [([21,21,21], 1)]
theorem eval_atom2587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2587 = ((g 21) * (g 21) * (g 21)) := by
  norm_num [atom2587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142457736960000 : Int) atom2587) := by
  rw [SparsePolynomial.eval_scale, eval_atom2587]
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 21) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2588 : SparsePolynomial.Poly := [([21,21,22], 1)]
theorem eval_atom2588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2588 = ((g 21) * (g 21) * (g 22)) := by
  norm_num [atom2588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (462137151168000 : Int) atom2588) := by
  rw [SparsePolynomial.eval_scale, eval_atom2588]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 21) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2589 : SparsePolynomial.Poly := [([21,21,23], 1)]
theorem eval_atom2589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2589 = ((g 21) * (g 21) * (g 23)) := by
  norm_num [atom2589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340707877171200 : Int) atom2589) := by
  rw [SparsePolynomial.eval_scale, eval_atom2589]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2590 : SparsePolynomial.Poly := [([21,22,22], 1)]
theorem eval_atom2590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2590 = ((g 21) * (g 22) * (g 22)) := by
  norm_num [atom2590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483215266548000 : Int) atom2590) := by
  rw [SparsePolynomial.eval_scale, eval_atom2590]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 21) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2591 : SparsePolynomial.Poly := [([21,22,23], 1)]
theorem eval_atom2591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2591 = ((g 21) * (g 22) * (g 23)) := by
  norm_num [atom2591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (732288178944000 : Int) atom2591) := by
  rw [SparsePolynomial.eval_scale, eval_atom2591]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2592 : SparsePolynomial.Poly := [([21,23,23], 1)]
theorem eval_atom2592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2592 = ((g 21) * (g 23) * (g 23)) := by
  norm_num [atom2592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211262697676800 : Int) atom2592) := by
  rw [SparsePolynomial.eval_scale, eval_atom2592]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2593 : SparsePolynomial.Poly := [([22,22,22], 1)]
theorem eval_atom2593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2593 = ((g 22) * (g 22) * (g 22)) := by
  norm_num [atom2593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167478850224000 : Int) atom2593) := by
  rw [SparsePolynomial.eval_scale, eval_atom2593]
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 22) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2594 : SparsePolynomial.Poly := [([22,22,23], 1)]
theorem eval_atom2594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2594 = ((g 22) * (g 22) * (g 23)) := by
  norm_num [atom2594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379428929838000 : Int) atom2594) := by
  rw [SparsePolynomial.eval_scale, eval_atom2594]
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 22) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2595 : SparsePolynomial.Poly := [([22,23,23], 1)]
theorem eval_atom2595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2595 = ((g 22) * (g 23) * (g 23)) := by
  norm_num [atom2595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215528053708800 : Int) atom2595) := by
  rw [SparsePolynomial.eval_scale, eval_atom2595]
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 22) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block034 : SparsePolynomial.Poly := [([17,19,21], 636169476096000), ([17,19,22], 597975854515200), ([17,19,23], 820556564889600), ([17,20,20], 368221356518400), ([17,20,21], 781603941888000), ([17,20,22], 761659858713600), ([17,20,23], 841818913689600), ([17,21,21], 357887855001600), ([17,21,22], 784623195417600), ([17,21,23], 883152919756800), ([17,22,22], 397355445648000), ([17,22,23], 924486925824000), ([17,23,23], 472874637312000), ([18,18,18], 10354763865600), ([18,18,19], 76586980377600), ([18,18,20], 262951467609600), ([18,18,21], 308474156390400), ([18,18,22], 220891320115200), ([18,18,23], 399519533952000), ([18,19,19], 72104877250560), ([18,19,20], 519184032998400), ([18,19,21], 700041571891200), ([18,19,22], 614688060672000), ([18,19,23], 850493952000000), ([18,20,20], 397074363840000), ([18,20,21], 853555730227200), ([18,20,22], 787472350156800), ([18,20,23], 761107037644800), ([18,21,21], 397903595443200), ([18,21,22], 819535972147200), ([18,21,23], 812561921740800), ([18,22,22], 418743032904000), ([18,22,23], 863774543923200), ([18,23,23], 387314945740800), ([19,19,20], 185526750689280), ([19,19,21], 315329137643520), ([19,19,22], 309576576960000), ([19,19,23], 429193267937280), ([19,20,20], 325313936640000), ([19,20,21], 794701548748800), ([19,20,22], 813284841600000), ([19,20,23], 801165302784000), ([19,21,21], 407726800588800), ([19,21,22], 854448748876800), ([19,21,23], 862741064908800), ([19,22,22], 440130620160000), ([19,22,23], 924074565120000), ([19,23,23], 422525395353600), ([20,20,20], 131465102630400), ([20,20,21], 403134133248000), ([20,20,22], 419548666521600), ([20,20,23], 279769985510400), ([20,21,21], 417550005734400), ([20,21,22], 889361525606400), ([20,21,23], 631236611174400), ([20,22,22], 461518207416000), ([20,22,23], 671988157747200), ([20,23,23], 176052248064000), ([21,21,21], 142457736960000), ([21,21,22], 462137151168000), ([21,21,23], 340707877171200), ([21,22,22], 483215266548000), ([21,22,23], 732288178944000), ([21,23,23], 211262697676800), ([22,22,22], 167478850224000), ([22,22,23], 379428929838000), ([22,23,23], 215528053708800)]
theorem block034_data : block034 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (636169476096000 : Int) atom2529) (SparsePolynomial.scale (597975854515200 : Int) atom2530)) (SparsePolynomial.merge (SparsePolynomial.scale (820556564889600 : Int) atom2531) (SparsePolynomial.scale (368221356518400 : Int) atom2532))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (781603941888000 : Int) atom2533) (SparsePolynomial.scale (761659858713600 : Int) atom2534)) (SparsePolynomial.merge (SparsePolynomial.scale (841818913689600 : Int) atom2535) (SparsePolynomial.scale (357887855001600 : Int) atom2536)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (784623195417600 : Int) atom2537) (SparsePolynomial.scale (883152919756800 : Int) atom2538)) (SparsePolynomial.merge (SparsePolynomial.scale (397355445648000 : Int) atom2539) (SparsePolynomial.scale (924486925824000 : Int) atom2540))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (472874637312000 : Int) atom2541) (SparsePolynomial.scale (10354763865600 : Int) atom2542)) (SparsePolynomial.merge (SparsePolynomial.scale (76586980377600 : Int) atom2543) (SparsePolynomial.scale (262951467609600 : Int) atom2544))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (308474156390400 : Int) atom2545) (SparsePolynomial.scale (220891320115200 : Int) atom2546)) (SparsePolynomial.merge (SparsePolynomial.scale (399519533952000 : Int) atom2547) (SparsePolynomial.scale (72104877250560 : Int) atom2548))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (519184032998400 : Int) atom2549) (SparsePolynomial.scale (700041571891200 : Int) atom2550)) (SparsePolynomial.merge (SparsePolynomial.scale (614688060672000 : Int) atom2551) (SparsePolynomial.scale (850493952000000 : Int) atom2552)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (397074363840000 : Int) atom2553) (SparsePolynomial.scale (853555730227200 : Int) atom2554)) (SparsePolynomial.merge (SparsePolynomial.scale (787472350156800 : Int) atom2555) (SparsePolynomial.scale (761107037644800 : Int) atom2556))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (397903595443200 : Int) atom2557) (SparsePolynomial.scale (819535972147200 : Int) atom2558)) (SparsePolynomial.merge (SparsePolynomial.scale (812561921740800 : Int) atom2559) (SparsePolynomial.merge (SparsePolynomial.scale (418743032904000 : Int) atom2560) (SparsePolynomial.scale (863774543923200 : Int) atom2561))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (387314945740800 : Int) atom2562) (SparsePolynomial.scale (185526750689280 : Int) atom2563)) (SparsePolynomial.merge (SparsePolynomial.scale (315329137643520 : Int) atom2564) (SparsePolynomial.scale (309576576960000 : Int) atom2565))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (429193267937280 : Int) atom2566) (SparsePolynomial.scale (325313936640000 : Int) atom2567)) (SparsePolynomial.merge (SparsePolynomial.scale (794701548748800 : Int) atom2568) (SparsePolynomial.scale (813284841600000 : Int) atom2569)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (801165302784000 : Int) atom2570) (SparsePolynomial.scale (407726800588800 : Int) atom2571)) (SparsePolynomial.merge (SparsePolynomial.scale (854448748876800 : Int) atom2572) (SparsePolynomial.scale (862741064908800 : Int) atom2573))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (440130620160000 : Int) atom2574) (SparsePolynomial.scale (924074565120000 : Int) atom2575)) (SparsePolynomial.merge (SparsePolynomial.scale (422525395353600 : Int) atom2576) (SparsePolynomial.merge (SparsePolynomial.scale (131465102630400 : Int) atom2577) (SparsePolynomial.scale (403134133248000 : Int) atom2578)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (419548666521600 : Int) atom2579) (SparsePolynomial.scale (279769985510400 : Int) atom2580)) (SparsePolynomial.merge (SparsePolynomial.scale (417550005734400 : Int) atom2581) (SparsePolynomial.scale (889361525606400 : Int) atom2582))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (631236611174400 : Int) atom2583) (SparsePolynomial.scale (461518207416000 : Int) atom2584)) (SparsePolynomial.merge (SparsePolynomial.scale (671988157747200 : Int) atom2585) (SparsePolynomial.scale (176052248064000 : Int) atom2586)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142457736960000 : Int) atom2587) (SparsePolynomial.scale (462137151168000 : Int) atom2588)) (SparsePolynomial.merge (SparsePolynomial.scale (340707877171200 : Int) atom2589) (SparsePolynomial.scale (483215266548000 : Int) atom2590))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (732288178944000 : Int) atom2591) (SparsePolynomial.scale (211262697676800 : Int) atom2592)) (SparsePolynomial.merge (SparsePolynomial.scale (167478850224000 : Int) atom2593) (SparsePolynomial.merge (SparsePolynomial.scale (379428929838000 : Int) atom2594) (SparsePolynomial.scale (215528053708800 : Int) atom2595)))))))) := by decide +kernel
theorem block034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block034 := by
  rw [block034_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2529_nonneg g hg hA hB) (atom2530_nonneg g hg hA hB)) (add_nonneg (atom2531_nonneg g hg hA hB) (atom2532_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2533_nonneg g hg hA hB) (atom2534_nonneg g hg hA hB)) (add_nonneg (atom2535_nonneg g hg hA hB) (atom2536_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2537_nonneg g hg hA hB) (atom2538_nonneg g hg hA hB)) (add_nonneg (atom2539_nonneg g hg hA hB) (atom2540_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2541_nonneg g hg hA hB) (atom2542_nonneg g hg hA hB)) (add_nonneg (atom2543_nonneg g hg hA hB) (atom2544_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2545_nonneg g hg hA hB) (atom2546_nonneg g hg hA hB)) (add_nonneg (atom2547_nonneg g hg hA hB) (atom2548_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2549_nonneg g hg hA hB) (atom2550_nonneg g hg hA hB)) (add_nonneg (atom2551_nonneg g hg hA hB) (atom2552_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2553_nonneg g hg hA hB) (atom2554_nonneg g hg hA hB)) (add_nonneg (atom2555_nonneg g hg hA hB) (atom2556_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2557_nonneg g hg hA hB) (atom2558_nonneg g hg hA hB)) (add_nonneg (atom2559_nonneg g hg hA hB) (add_nonneg (atom2560_nonneg g hg hA hB) (atom2561_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2562_nonneg g hg hA hB) (atom2563_nonneg g hg hA hB)) (add_nonneg (atom2564_nonneg g hg hA hB) (atom2565_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2566_nonneg g hg hA hB) (atom2567_nonneg g hg hA hB)) (add_nonneg (atom2568_nonneg g hg hA hB) (atom2569_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2570_nonneg g hg hA hB) (atom2571_nonneg g hg hA hB)) (add_nonneg (atom2572_nonneg g hg hA hB) (atom2573_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2574_nonneg g hg hA hB) (atom2575_nonneg g hg hA hB)) (add_nonneg (atom2576_nonneg g hg hA hB) (add_nonneg (atom2577_nonneg g hg hA hB) (atom2578_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2579_nonneg g hg hA hB) (atom2580_nonneg g hg hA hB)) (add_nonneg (atom2581_nonneg g hg hA hB) (atom2582_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2583_nonneg g hg hA hB) (atom2584_nonneg g hg hA hB)) (add_nonneg (atom2585_nonneg g hg hA hB) (atom2586_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2587_nonneg g hg hA hB) (atom2588_nonneg g hg hA hB)) (add_nonneg (atom2589_nonneg g hg hA hB) (atom2590_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2591_nonneg g hg hA hB) (atom2592_nonneg g hg hA hB)) (add_nonneg (atom2593_nonneg g hg hA hB) (add_nonneg (atom2594_nonneg g hg hA hB) (atom2595_nonneg g hg hA hB))))))))

end APPT.Finite24
