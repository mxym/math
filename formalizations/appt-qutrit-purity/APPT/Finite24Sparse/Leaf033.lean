import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2449 : SparsePolynomial.Poly := [([15,15,21], 1)]
theorem eval_atom2449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2449 = ((g 15) * (g 15) * (g 21)) := by
  norm_num [atom2449, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65163300249600 : Int) atom2449) := by
  rw [SparsePolynomial.eval_scale, eval_atom2449]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2450 : SparsePolynomial.Poly := [([15,15,23], 1)]
theorem eval_atom2450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2450 = ((g 15) * (g 15) * (g 23)) := by
  norm_num [atom2450, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5211208396800 : Int) atom2450) := by
  rw [SparsePolynomial.eval_scale, eval_atom2450]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2451 : SparsePolynomial.Poly := [([15,16,18], 1)]
theorem eval_atom2451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2451 = ((g 15) * (g 16) * (g 18)) := by
  norm_num [atom2451, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24896019778560 : Int) atom2451) := by
  rw [SparsePolynomial.eval_scale, eval_atom2451]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2452 : SparsePolynomial.Poly := [([15,16,20], 1)]
theorem eval_atom2452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2452 = ((g 15) * (g 16) * (g 20)) := by
  norm_num [atom2452, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (233856198374400 : Int) atom2452) := by
  rw [SparsePolynomial.eval_scale, eval_atom2452]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2453 : SparsePolynomial.Poly := [([15,16,21], 1)]
theorem eval_atom2453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2453 = ((g 15) * (g 16) * (g 21)) := by
  norm_num [atom2453, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220828821696000 : Int) atom2453) := by
  rw [SparsePolynomial.eval_scale, eval_atom2453]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2454 : SparsePolynomial.Poly := [([15,16,22], 1)]
theorem eval_atom2454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2454 = ((g 15) * (g 16) * (g 22)) := by
  norm_num [atom2454, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99469520156160 : Int) atom2454) := by
  rw [SparsePolynomial.eval_scale, eval_atom2454]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2455 : SparsePolynomial.Poly := [([15,16,23], 1)]
theorem eval_atom2455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2455 = ((g 15) * (g 16) * (g 23)) := by
  norm_num [atom2455, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (259121345414400 : Int) atom2455) := by
  rw [SparsePolynomial.eval_scale, eval_atom2455]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2456 : SparsePolynomial.Poly := [([15,17,17], 1)]
theorem eval_atom2456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2456 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom2456, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8561639116800 : Int) atom2456) := by
  rw [SparsePolynomial.eval_scale, eval_atom2456]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2457 : SparsePolynomial.Poly := [([15,17,18], 1)]
theorem eval_atom2457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2457 = ((g 15) * (g 17) * (g 18)) := by
  norm_num [atom2457, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35057102976000 : Int) atom2457) := by
  rw [SparsePolynomial.eval_scale, eval_atom2457]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2458 : SparsePolynomial.Poly := [([15,17,19], 1)]
theorem eval_atom2458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2458 = ((g 15) * (g 17) * (g 19)) := by
  norm_num [atom2458, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40411348992000 : Int) atom2458) := by
  rw [SparsePolynomial.eval_scale, eval_atom2458]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2459 : SparsePolynomial.Poly := [([15,17,20], 1)]
theorem eval_atom2459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2459 = ((g 15) * (g 17) * (g 20)) := by
  norm_num [atom2459, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (327449191910400 : Int) atom2459) := by
  rw [SparsePolynomial.eval_scale, eval_atom2459]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2460 : SparsePolynomial.Poly := [([15,17,21], 1)]
theorem eval_atom2460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2460 = ((g 15) * (g 17) * (g 21)) := by
  norm_num [atom2460, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (349177379443200 : Int) atom2460) := by
  rw [SparsePolynomial.eval_scale, eval_atom2460]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2461 : SparsePolynomial.Poly := [([15,17,22], 1)]
theorem eval_atom2461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2461 = ((g 15) * (g 17) * (g 22)) := by
  norm_num [atom2461, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (284381337945600 : Int) atom2461) := by
  rw [SparsePolynomial.eval_scale, eval_atom2461]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2462 : SparsePolynomial.Poly := [([15,17,23], 1)]
theorem eval_atom2462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2462 = ((g 15) * (g 17) * (g 23)) := by
  norm_num [atom2462, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (503972755372800 : Int) atom2462) := by
  rw [SparsePolynomial.eval_scale, eval_atom2462]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2463 : SparsePolynomial.Poly := [([15,18,18], 1)]
theorem eval_atom2463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2463 = ((g 15) * (g 18) * (g 18)) := by
  norm_num [atom2463, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71490459801600 : Int) atom2463) := by
  rw [SparsePolynomial.eval_scale, eval_atom2463]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2464 : SparsePolynomial.Poly := [([15,18,19], 1)]
theorem eval_atom2464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2464 = ((g 15) * (g 18) * (g 19)) := by
  norm_num [atom2464, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197412532531200 : Int) atom2464) := by
  rw [SparsePolynomial.eval_scale, eval_atom2464]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2465 : SparsePolynomial.Poly := [([15,18,20], 1)]
theorem eval_atom2465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2465 = ((g 15) * (g 18) * (g 20)) := by
  norm_num [atom2465, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (533527742361600 : Int) atom2465) := by
  rw [SparsePolynomial.eval_scale, eval_atom2465]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2466 : SparsePolynomial.Poly := [([15,18,21], 1)]
theorem eval_atom2466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2466 = ((g 15) * (g 18) * (g 21)) := by
  norm_num [atom2466, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (587959355289600 : Int) atom2466) := by
  rw [SparsePolynomial.eval_scale, eval_atom2466]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2467 : SparsePolynomial.Poly := [([15,18,22], 1)]
theorem eval_atom2467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2467 = ((g 15) * (g 18) * (g 22)) := by
  norm_num [atom2467, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (457214273107200 : Int) atom2467) := by
  rw [SparsePolynomial.eval_scale, eval_atom2467]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2468 : SparsePolynomial.Poly := [([15,18,23], 1)]
theorem eval_atom2468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2468 = ((g 15) * (g 18) * (g 23)) := by
  norm_num [atom2468, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (739589540659200 : Int) atom2468) := by
  rw [SparsePolynomial.eval_scale, eval_atom2468]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2469 : SparsePolynomial.Poly := [([15,19,19], 1)]
theorem eval_atom2469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2469 = ((g 15) * (g 19) * (g 19)) := by
  norm_num [atom2469, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86391113840640 : Int) atom2469) := by
  rw [SparsePolynomial.eval_scale, eval_atom2469]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2470 : SparsePolynomial.Poly := [([15,19,20], 1)]
theorem eval_atom2470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2470 = ((g 15) * (g 19) * (g 20)) := by
  norm_num [atom2470, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (505631540736000 : Int) atom2470) := by
  rw [SparsePolynomial.eval_scale, eval_atom2470]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2471 : SparsePolynomial.Poly := [([15,19,21], 1)]
theorem eval_atom2471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2471 = ((g 15) * (g 19) * (g 21)) := by
  norm_num [atom2471, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (646813536768000 : Int) atom2471) := by
  rw [SparsePolynomial.eval_scale, eval_atom2471]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2472 : SparsePolynomial.Poly := [([15,19,22], 1)]
theorem eval_atom2472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2472 = ((g 15) * (g 19) * (g 22)) := by
  norm_num [atom2472, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (564551442201600 : Int) atom2472) := by
  rw [SparsePolynomial.eval_scale, eval_atom2472]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2473 : SparsePolynomial.Poly := [([15,19,23], 1)]
theorem eval_atom2473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2473 = ((g 15) * (g 19) * (g 23)) := by
  norm_num [atom2473, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (760681790668800 : Int) atom2473) := by
  rw [SparsePolynomial.eval_scale, eval_atom2473]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2474 : SparsePolynomial.Poly := [([15,20,20], 1)]
theorem eval_atom2474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2474 = ((g 15) * (g 20) * (g 20)) := by
  norm_num [atom2474, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (379709468006400 : Int) atom2474) := by
  rw [SparsePolynomial.eval_scale, eval_atom2474]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2475 : SparsePolynomial.Poly := [([15,20,21], 1)]
theorem eval_atom2475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2475 = ((g 15) * (g 20) * (g 21)) := by
  norm_num [atom2475, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (776088617472000 : Int) atom2475) := by
  rw [SparsePolynomial.eval_scale, eval_atom2475]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2476 : SparsePolynomial.Poly := [([15,20,22], 1)]
theorem eval_atom2476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2476 = ((g 15) * (g 20) * (g 22)) := by
  norm_num [atom2476, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (671767480339200 : Int) atom2476) := by
  rw [SparsePolynomial.eval_scale, eval_atom2476]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2477 : SparsePolynomial.Poly := [([15,20,23], 1)]
theorem eval_atom2477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2477 = ((g 15) * (g 20) * (g 23)) := by
  norm_num [atom2477, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (726466161254400 : Int) atom2477) := by
  rw [SparsePolynomial.eval_scale, eval_atom2477]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2478 : SparsePolynomial.Poly := [([15,21,21], 1)]
theorem eval_atom2478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2478 = ((g 15) * (g 21) * (g 21)) := by
  norm_num [atom2478, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (347050500249600 : Int) atom2478) := by
  rw [SparsePolynomial.eval_scale, eval_atom2478]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2479 : SparsePolynomial.Poly := [([15,21,22], 1)]
theorem eval_atom2479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2479 = ((g 15) * (g 21) * (g 22)) := by
  norm_num [atom2479, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (657396548726400 : Int) atom2479) := by
  rw [SparsePolynomial.eval_scale, eval_atom2479]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2480 : SparsePolynomial.Poly := [([15,21,23], 1)]
theorem eval_atom2480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2480 = ((g 15) * (g 21) * (g 23)) := by
  norm_num [atom2480, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (747558411264000 : Int) atom2480) := by
  rw [SparsePolynomial.eval_scale, eval_atom2480]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2481 : SparsePolynomial.Poly := [([15,22,22], 1)]
theorem eval_atom2481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2481 = ((g 15) * (g 22) * (g 22)) := by
  norm_num [atom2481, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (276807592656000 : Int) atom2481) := by
  rw [SparsePolynomial.eval_scale, eval_atom2481]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2482 : SparsePolynomial.Poly := [([15,22,23], 1)]
theorem eval_atom2482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2482 = ((g 15) * (g 22) * (g 23)) := by
  norm_num [atom2482, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (682549021425600 : Int) atom2482) := by
  rw [SparsePolynomial.eval_scale, eval_atom2482]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2483 : SparsePolynomial.Poly := [([15,23,23], 1)]
theorem eval_atom2483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2483 = ((g 15) * (g 23) * (g 23)) := by
  norm_num [atom2483, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (367217515929600 : Int) atom2483) := by
  rw [SparsePolynomial.eval_scale, eval_atom2483]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2484 : SparsePolynomial.Poly := [([16,16,16], 1)]
theorem eval_atom2484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2484 = ((g 16) * (g 16) * (g 16)) := by
  norm_num [atom2484, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1027680192000 : Int) atom2484) := by
  rw [SparsePolynomial.eval_scale, eval_atom2484]
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 16) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2485 : SparsePolynomial.Poly := [([16,16,18], 1)]
theorem eval_atom2485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2485 = ((g 16) * (g 16) * (g 18)) := by
  norm_num [atom2485, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7461795801600 : Int) atom2485) := by
  rw [SparsePolynomial.eval_scale, eval_atom2485]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2486 : SparsePolynomial.Poly := [([16,16,20], 1)]
theorem eval_atom2486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2486 = ((g 16) * (g 16) * (g 20)) := by
  norm_num [atom2486, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109950182899200 : Int) atom2486) := by
  rw [SparsePolynomial.eval_scale, eval_atom2486]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2487 : SparsePolynomial.Poly := [([16,16,21], 1)]
theorem eval_atom2487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2487 = ((g 16) * (g 16) * (g 21)) := by
  norm_num [atom2487, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102488387097600 : Int) atom2487) := by
  rw [SparsePolynomial.eval_scale, eval_atom2487]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2488 : SparsePolynomial.Poly := [([16,16,23], 1)]
theorem eval_atom2488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2488 = ((g 16) * (g 16) * (g 23)) := by
  norm_num [atom2488, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102213909504000 : Int) atom2488) := by
  rw [SparsePolynomial.eval_scale, eval_atom2488]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2489 : SparsePolynomial.Poly := [([16,17,17], 1)]
theorem eval_atom2489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2489 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom2489, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2395557964800 : Int) atom2489) := by
  rw [SparsePolynomial.eval_scale, eval_atom2489]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2490 : SparsePolynomial.Poly := [([16,17,19], 1)]
theorem eval_atom2490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2490 = ((g 16) * (g 17) * (g 19)) := by
  norm_num [atom2490, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9886777420800 : Int) atom2490) := by
  rw [SparsePolynomial.eval_scale, eval_atom2490]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2491 : SparsePolynomial.Poly := [([16,17,20], 1)]
theorem eval_atom2491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2491 = ((g 16) * (g 17) * (g 20)) := by
  norm_num [atom2491, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (292154122444800 : Int) atom2491) := by
  rw [SparsePolynomial.eval_scale, eval_atom2491]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2492 : SparsePolynomial.Poly := [([16,17,21], 1)]
theorem eval_atom2492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2492 = ((g 16) * (g 17) * (g 21)) := by
  norm_num [atom2492, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (317089058764800 : Int) atom2492) := by
  rw [SparsePolynomial.eval_scale, eval_atom2492]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2493 : SparsePolynomial.Poly := [([16,17,22], 1)]
theorem eval_atom2493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2493 = ((g 16) * (g 17) * (g 22)) := by
  norm_num [atom2493, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188403739776000 : Int) atom2493) := by
  rw [SparsePolynomial.eval_scale, eval_atom2493]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2494 : SparsePolynomial.Poly := [([16,17,23], 1)]
theorem eval_atom2494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2494 = ((g 16) * (g 17) * (g 23)) := by
  norm_num [atom2494, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (477770776358400 : Int) atom2494) := by
  rw [SparsePolynomial.eval_scale, eval_atom2494]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2495 : SparsePolynomial.Poly := [([16,18,18], 1)]
theorem eval_atom2495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2495 = ((g 16) * (g 18) * (g 18)) := by
  norm_num [atom2495, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41516346816000 : Int) atom2495) := by
  rw [SparsePolynomial.eval_scale, eval_atom2495]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2496 : SparsePolynomial.Poly := [([16,18,19], 1)]
theorem eval_atom2496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2496 = ((g 16) * (g 18) * (g 19)) := by
  norm_num [atom2496, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149668894771200 : Int) atom2496) := by
  rw [SparsePolynomial.eval_scale, eval_atom2496]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2497 : SparsePolynomial.Poly := [([16,18,20], 1)]
theorem eval_atom2497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2497 = ((g 16) * (g 18) * (g 20)) := by
  norm_num [atom2497, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (497988692812800 : Int) atom2497) := by
  rw [SparsePolynomial.eval_scale, eval_atom2497]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2498 : SparsePolynomial.Poly := [([16,18,21], 1)]
theorem eval_atom2498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2498 = ((g 16) * (g 18) * (g 21)) := by
  norm_num [atom2498, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (564624893952000 : Int) atom2498) := by
  rw [SparsePolynomial.eval_scale, eval_atom2498]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2499 : SparsePolynomial.Poly := [([16,18,22], 1)]
theorem eval_atom2499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2499 = ((g 16) * (g 18) * (g 22)) := by
  norm_num [atom2499, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (426558798489600 : Int) atom2499) := by
  rw [SparsePolynomial.eval_scale, eval_atom2499]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2500 : SparsePolynomial.Poly := [([16,18,23], 1)]
theorem eval_atom2500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2500 = ((g 16) * (g 18) * (g 23)) := by
  norm_num [atom2500, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (759406049740800 : Int) atom2500) := by
  rw [SparsePolynomial.eval_scale, eval_atom2500]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2501 : SparsePolynomial.Poly := [([16,19,19], 1)]
theorem eval_atom2501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2501 = ((g 16) * (g 19) * (g 19)) := by
  norm_num [atom2501, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65538548490240 : Int) atom2501) := by
  rw [SparsePolynomial.eval_scale, eval_atom2501]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2502 : SparsePolynomial.Poly := [([16,19,20], 1)]
theorem eval_atom2502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2502 = ((g 16) * (g 19) * (g 20)) := by
  norm_num [atom2502, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (477151590988800 : Int) atom2502) := by
  rw [SparsePolynomial.eval_scale, eval_atom2502]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2503 : SparsePolynomial.Poly := [([16,19,21], 1)]
theorem eval_atom2503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2503 = ((g 16) * (g 19) * (g 21)) := by
  norm_num [atom2503, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (631558767974400 : Int) atom2503) := by
  rw [SparsePolynomial.eval_scale, eval_atom2503]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2504 : SparsePolynomial.Poly := [([16,19,22], 1)]
theorem eval_atom2504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2504 = ((g 16) * (g 19) * (g 22)) := by
  norm_num [atom2504, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (581263648358400 : Int) atom2504) := by
  rw [SparsePolynomial.eval_scale, eval_atom2504]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2505 : SparsePolynomial.Poly := [([16,19,23], 1)]
theorem eval_atom2505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2505 = ((g 16) * (g 19) * (g 23)) := by
  norm_num [atom2505, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (790619177779200 : Int) atom2505) := by
  rw [SparsePolynomial.eval_scale, eval_atom2505]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2506 : SparsePolynomial.Poly := [([16,20,20], 1)]
theorem eval_atom2506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2506 = ((g 16) * (g 20) * (g 20)) := by
  norm_num [atom2506, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (368999043033600 : Int) atom2506) := by
  rw [SparsePolynomial.eval_scale, eval_atom2506]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2507 : SparsePolynomial.Poly := [([16,20,21], 1)]
theorem eval_atom2507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2507 = ((g 16) * (g 20) * (g 21)) := by
  norm_num [atom2507, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (768913541222400 : Int) atom2507) := by
  rw [SparsePolynomial.eval_scale, eval_atom2507]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2508 : SparsePolynomial.Poly := [([16,20,22], 1)]
theorem eval_atom2508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2508 = ((g 16) * (g 20) * (g 22)) := by
  norm_num [atom2508, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (735847367270400 : Int) atom2508) := by
  rw [SparsePolynomial.eval_scale, eval_atom2508]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2509 : SparsePolynomial.Poly := [([16,20,23], 1)]
theorem eval_atom2509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2509 = ((g 16) * (g 20) * (g 23)) := by
  norm_num [atom2509, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (804008014387200 : Int) atom2509) := by
  rw [SparsePolynomial.eval_scale, eval_atom2509]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2510 : SparsePolynomial.Poly := [([16,21,21], 1)]
theorem eval_atom2510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2510 = ((g 16) * (g 21) * (g 21)) := by
  norm_num [atom2510, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (347502808396800 : Int) atom2510) := by
  rw [SparsePolynomial.eval_scale, eval_atom2510]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2511 : SparsePolynomial.Poly := [([16,21,22], 1)]
theorem eval_atom2511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2511 = ((g 16) * (g 21) * (g 22)) := by
  norm_num [atom2511, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (749710418688000 : Int) atom2511) := by
  rw [SparsePolynomial.eval_scale, eval_atom2511]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2512 : SparsePolynomial.Poly := [([16,21,23], 1)]
theorem eval_atom2512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2512 = ((g 16) * (g 21) * (g 23)) := by
  norm_num [atom2512, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (835221142425600 : Int) atom2512) := by
  rw [SparsePolynomial.eval_scale, eval_atom2512]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2513 : SparsePolynomial.Poly := [([16,22,22], 1)]
theorem eval_atom2513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2513 = ((g 16) * (g 22) * (g 22)) := by
  norm_num [atom2513, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (375348914640000 : Int) atom2513) := by
  rw [SparsePolynomial.eval_scale, eval_atom2513]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2514 : SparsePolynomial.Poly := [([16,22,23], 1)]
theorem eval_atom2514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2514 = ((g 16) * (g 22) * (g 23)) := by
  norm_num [atom2514, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (866434270464000 : Int) atom2514) := by
  rw [SparsePolynomial.eval_scale, eval_atom2514]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2515 : SparsePolynomial.Poly := [([16,23,23], 1)]
theorem eval_atom2515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2515 = ((g 16) * (g 23) * (g 23)) := by
  norm_num [atom2515, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (439911553536000 : Int) atom2515) := by
  rw [SparsePolynomial.eval_scale, eval_atom2515]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2516 : SparsePolynomial.Poly := [([17,17,19], 1)]
theorem eval_atom2516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2516 = ((g 17) * (g 17) * (g 19)) := by
  norm_num [atom2516, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14841119462400 : Int) atom2516) := by
  rw [SparsePolynomial.eval_scale, eval_atom2516]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2517 : SparsePolynomial.Poly := [([17,17,20], 1)]
theorem eval_atom2517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2517 = ((g 17) * (g 17) * (g 20)) := by
  norm_num [atom2517, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (155130096844800 : Int) atom2517) := by
  rw [SparsePolynomial.eval_scale, eval_atom2517]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2518 : SparsePolynomial.Poly := [([17,17,21], 1)]
theorem eval_atom2518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2518 = ((g 17) * (g 17) * (g 21)) := by
  norm_num [atom2518, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (169971216307200 : Int) atom2518) := by
  rw [SparsePolynomial.eval_scale, eval_atom2518]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2519 : SparsePolynomial.Poly := [([17,17,22], 1)]
theorem eval_atom2519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2519 = ((g 17) * (g 17) * (g 22)) := by
  norm_num [atom2519, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96697940774400 : Int) atom2519) := by
  rw [SparsePolynomial.eval_scale, eval_atom2519]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2520 : SparsePolynomial.Poly := [([17,17,23], 1)]
theorem eval_atom2520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2520 = ((g 17) * (g 17) * (g 23)) := by
  norm_num [atom2520, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229250644761600 : Int) atom2520) := by
  rw [SparsePolynomial.eval_scale, eval_atom2520]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2521 : SparsePolynomial.Poly := [([17,18,18], 1)]
theorem eval_atom2521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2521 = ((g 17) * (g 18) * (g 18)) := by
  norm_num [atom2521, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21474972288000 : Int) atom2521) := by
  rw [SparsePolynomial.eval_scale, eval_atom2521]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2522 : SparsePolynomial.Poly := [([17,18,19], 1)]
theorem eval_atom2522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2522 = ((g 17) * (g 18) * (g 19)) := by
  norm_num [atom2522, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121790733926400 : Int) atom2522) := by
  rw [SparsePolynomial.eval_scale, eval_atom2522]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2523 : SparsePolynomial.Poly := [([17,18,20], 1)]
theorem eval_atom2523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2523 = ((g 17) * (g 18) * (g 20)) := by
  norm_num [atom2523, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (482315120179200 : Int) atom2523) := by
  rw [SparsePolynomial.eval_scale, eval_atom2523]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2524 : SparsePolynomial.Poly := [([17,18,21], 1)]
theorem eval_atom2524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2524 = ((g 17) * (g 18) * (g 21)) := by
  norm_num [atom2524, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (561155909529600 : Int) atom2524) := by
  rw [SparsePolynomial.eval_scale, eval_atom2524]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2525 : SparsePolynomial.Poly := [([17,18,22], 1)]
theorem eval_atom2525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2525 = ((g 17) * (g 18) * (g 22)) := by
  norm_num [atom2525, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (434170719360000 : Int) atom2525) := by
  rw [SparsePolynomial.eval_scale, eval_atom2525]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2526 : SparsePolynomial.Poly := [([17,18,23], 1)]
theorem eval_atom2526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2526 = ((g 17) * (g 18) * (g 23)) := by
  norm_num [atom2526, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (779222558822400 : Int) atom2526) := by
  rw [SparsePolynomial.eval_scale, eval_atom2526]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2527 : SparsePolynomial.Poly := [([17,19,19], 1)]
theorem eval_atom2527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2527 = ((g 17) * (g 19) * (g 19)) := by
  norm_num [atom2527, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54618721597440 : Int) atom2527) := by
  rw [SparsePolynomial.eval_scale, eval_atom2527]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2528 : SparsePolynomial.Poly := [([17,19,20], 1)]
theorem eval_atom2528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2528 = ((g 17) * (g 19) * (g 20)) := by
  norm_num [atom2528, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (468537118156800 : Int) atom2528) := by
  rw [SparsePolynomial.eval_scale, eval_atom2528]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block033 : SparsePolynomial.Poly := [([15,15,21], 65163300249600), ([15,15,23], 5211208396800), ([15,16,18], 24896019778560), ([15,16,20], 233856198374400), ([15,16,21], 220828821696000), ([15,16,22], 99469520156160), ([15,16,23], 259121345414400), ([15,17,17], 8561639116800), ([15,17,18], 35057102976000), ([15,17,19], 40411348992000), ([15,17,20], 327449191910400), ([15,17,21], 349177379443200), ([15,17,22], 284381337945600), ([15,17,23], 503972755372800), ([15,18,18], 71490459801600), ([15,18,19], 197412532531200), ([15,18,20], 533527742361600), ([15,18,21], 587959355289600), ([15,18,22], 457214273107200), ([15,18,23], 739589540659200), ([15,19,19], 86391113840640), ([15,19,20], 505631540736000), ([15,19,21], 646813536768000), ([15,19,22], 564551442201600), ([15,19,23], 760681790668800), ([15,20,20], 379709468006400), ([15,20,21], 776088617472000), ([15,20,22], 671767480339200), ([15,20,23], 726466161254400), ([15,21,21], 347050500249600), ([15,21,22], 657396548726400), ([15,21,23], 747558411264000), ([15,22,22], 276807592656000), ([15,22,23], 682549021425600), ([15,23,23], 367217515929600), ([16,16,16], 1027680192000), ([16,16,18], 7461795801600), ([16,16,20], 109950182899200), ([16,16,21], 102488387097600), ([16,16,23], 102213909504000), ([16,17,17], 2395557964800), ([16,17,19], 9886777420800), ([16,17,20], 292154122444800), ([16,17,21], 317089058764800), ([16,17,22], 188403739776000), ([16,17,23], 477770776358400), ([16,18,18], 41516346816000), ([16,18,19], 149668894771200), ([16,18,20], 497988692812800), ([16,18,21], 564624893952000), ([16,18,22], 426558798489600), ([16,18,23], 759406049740800), ([16,19,19], 65538548490240), ([16,19,20], 477151590988800), ([16,19,21], 631558767974400), ([16,19,22], 581263648358400), ([16,19,23], 790619177779200), ([16,20,20], 368999043033600), ([16,20,21], 768913541222400), ([16,20,22], 735847367270400), ([16,20,23], 804008014387200), ([16,21,21], 347502808396800), ([16,21,22], 749710418688000), ([16,21,23], 835221142425600), ([16,22,22], 375348914640000), ([16,22,23], 866434270464000), ([16,23,23], 439911553536000), ([17,17,19], 14841119462400), ([17,17,20], 155130096844800), ([17,17,21], 169971216307200), ([17,17,22], 96697940774400), ([17,17,23], 229250644761600), ([17,18,18], 21474972288000), ([17,18,19], 121790733926400), ([17,18,20], 482315120179200), ([17,18,21], 561155909529600), ([17,18,22], 434170719360000), ([17,18,23], 779222558822400), ([17,19,19], 54618721597440), ([17,19,20], 468537118156800)]
theorem block033_data : block033 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (65163300249600 : Int) atom2449) (SparsePolynomial.scale (5211208396800 : Int) atom2450)) (SparsePolynomial.merge (SparsePolynomial.scale (24896019778560 : Int) atom2451) (SparsePolynomial.merge (SparsePolynomial.scale (233856198374400 : Int) atom2452) (SparsePolynomial.scale (220828821696000 : Int) atom2453)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (99469520156160 : Int) atom2454) (SparsePolynomial.scale (259121345414400 : Int) atom2455)) (SparsePolynomial.merge (SparsePolynomial.scale (8561639116800 : Int) atom2456) (SparsePolynomial.merge (SparsePolynomial.scale (35057102976000 : Int) atom2457) (SparsePolynomial.scale (40411348992000 : Int) atom2458))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (327449191910400 : Int) atom2459) (SparsePolynomial.scale (349177379443200 : Int) atom2460)) (SparsePolynomial.merge (SparsePolynomial.scale (284381337945600 : Int) atom2461) (SparsePolynomial.merge (SparsePolynomial.scale (503972755372800 : Int) atom2462) (SparsePolynomial.scale (71490459801600 : Int) atom2463)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (197412532531200 : Int) atom2464) (SparsePolynomial.scale (533527742361600 : Int) atom2465)) (SparsePolynomial.merge (SparsePolynomial.scale (587959355289600 : Int) atom2466) (SparsePolynomial.merge (SparsePolynomial.scale (457214273107200 : Int) atom2467) (SparsePolynomial.scale (739589540659200 : Int) atom2468)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (86391113840640 : Int) atom2469) (SparsePolynomial.scale (505631540736000 : Int) atom2470)) (SparsePolynomial.merge (SparsePolynomial.scale (646813536768000 : Int) atom2471) (SparsePolynomial.merge (SparsePolynomial.scale (564551442201600 : Int) atom2472) (SparsePolynomial.scale (760681790668800 : Int) atom2473)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (379709468006400 : Int) atom2474) (SparsePolynomial.scale (776088617472000 : Int) atom2475)) (SparsePolynomial.merge (SparsePolynomial.scale (671767480339200 : Int) atom2476) (SparsePolynomial.merge (SparsePolynomial.scale (726466161254400 : Int) atom2477) (SparsePolynomial.scale (347050500249600 : Int) atom2478))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (657396548726400 : Int) atom2479) (SparsePolynomial.scale (747558411264000 : Int) atom2480)) (SparsePolynomial.merge (SparsePolynomial.scale (276807592656000 : Int) atom2481) (SparsePolynomial.merge (SparsePolynomial.scale (682549021425600 : Int) atom2482) (SparsePolynomial.scale (367217515929600 : Int) atom2483)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1027680192000 : Int) atom2484) (SparsePolynomial.scale (7461795801600 : Int) atom2485)) (SparsePolynomial.merge (SparsePolynomial.scale (109950182899200 : Int) atom2486) (SparsePolynomial.merge (SparsePolynomial.scale (102488387097600 : Int) atom2487) (SparsePolynomial.scale (102213909504000 : Int) atom2488))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2395557964800 : Int) atom2489) (SparsePolynomial.scale (9886777420800 : Int) atom2490)) (SparsePolynomial.merge (SparsePolynomial.scale (292154122444800 : Int) atom2491) (SparsePolynomial.merge (SparsePolynomial.scale (317089058764800 : Int) atom2492) (SparsePolynomial.scale (188403739776000 : Int) atom2493)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (477770776358400 : Int) atom2494) (SparsePolynomial.scale (41516346816000 : Int) atom2495)) (SparsePolynomial.merge (SparsePolynomial.scale (149668894771200 : Int) atom2496) (SparsePolynomial.merge (SparsePolynomial.scale (497988692812800 : Int) atom2497) (SparsePolynomial.scale (564624893952000 : Int) atom2498))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (426558798489600 : Int) atom2499) (SparsePolynomial.scale (759406049740800 : Int) atom2500)) (SparsePolynomial.merge (SparsePolynomial.scale (65538548490240 : Int) atom2501) (SparsePolynomial.merge (SparsePolynomial.scale (477151590988800 : Int) atom2502) (SparsePolynomial.scale (631558767974400 : Int) atom2503)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (581263648358400 : Int) atom2504) (SparsePolynomial.scale (790619177779200 : Int) atom2505)) (SparsePolynomial.merge (SparsePolynomial.scale (368999043033600 : Int) atom2506) (SparsePolynomial.merge (SparsePolynomial.scale (768913541222400 : Int) atom2507) (SparsePolynomial.scale (735847367270400 : Int) atom2508)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (804008014387200 : Int) atom2509) (SparsePolynomial.scale (347502808396800 : Int) atom2510)) (SparsePolynomial.merge (SparsePolynomial.scale (749710418688000 : Int) atom2511) (SparsePolynomial.merge (SparsePolynomial.scale (835221142425600 : Int) atom2512) (SparsePolynomial.scale (375348914640000 : Int) atom2513)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (866434270464000 : Int) atom2514) (SparsePolynomial.scale (439911553536000 : Int) atom2515)) (SparsePolynomial.merge (SparsePolynomial.scale (14841119462400 : Int) atom2516) (SparsePolynomial.merge (SparsePolynomial.scale (155130096844800 : Int) atom2517) (SparsePolynomial.scale (169971216307200 : Int) atom2518))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (96697940774400 : Int) atom2519) (SparsePolynomial.scale (229250644761600 : Int) atom2520)) (SparsePolynomial.merge (SparsePolynomial.scale (21474972288000 : Int) atom2521) (SparsePolynomial.merge (SparsePolynomial.scale (121790733926400 : Int) atom2522) (SparsePolynomial.scale (482315120179200 : Int) atom2523)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (561155909529600 : Int) atom2524) (SparsePolynomial.scale (434170719360000 : Int) atom2525)) (SparsePolynomial.merge (SparsePolynomial.scale (779222558822400 : Int) atom2526) (SparsePolynomial.merge (SparsePolynomial.scale (54618721597440 : Int) atom2527) (SparsePolynomial.scale (468537118156800 : Int) atom2528)))))))) := by decide +kernel
theorem block033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block033 := by
  rw [block033_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2449_nonneg g hg hA hB) (atom2450_nonneg g hg hA hB)) (add_nonneg (atom2451_nonneg g hg hA hB) (add_nonneg (atom2452_nonneg g hg hA hB) (atom2453_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2454_nonneg g hg hA hB) (atom2455_nonneg g hg hA hB)) (add_nonneg (atom2456_nonneg g hg hA hB) (add_nonneg (atom2457_nonneg g hg hA hB) (atom2458_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2459_nonneg g hg hA hB) (atom2460_nonneg g hg hA hB)) (add_nonneg (atom2461_nonneg g hg hA hB) (add_nonneg (atom2462_nonneg g hg hA hB) (atom2463_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2464_nonneg g hg hA hB) (atom2465_nonneg g hg hA hB)) (add_nonneg (atom2466_nonneg g hg hA hB) (add_nonneg (atom2467_nonneg g hg hA hB) (atom2468_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2469_nonneg g hg hA hB) (atom2470_nonneg g hg hA hB)) (add_nonneg (atom2471_nonneg g hg hA hB) (add_nonneg (atom2472_nonneg g hg hA hB) (atom2473_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2474_nonneg g hg hA hB) (atom2475_nonneg g hg hA hB)) (add_nonneg (atom2476_nonneg g hg hA hB) (add_nonneg (atom2477_nonneg g hg hA hB) (atom2478_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2479_nonneg g hg hA hB) (atom2480_nonneg g hg hA hB)) (add_nonneg (atom2481_nonneg g hg hA hB) (add_nonneg (atom2482_nonneg g hg hA hB) (atom2483_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2484_nonneg g hg hA hB) (atom2485_nonneg g hg hA hB)) (add_nonneg (atom2486_nonneg g hg hA hB) (add_nonneg (atom2487_nonneg g hg hA hB) (atom2488_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2489_nonneg g hg hA hB) (atom2490_nonneg g hg hA hB)) (add_nonneg (atom2491_nonneg g hg hA hB) (add_nonneg (atom2492_nonneg g hg hA hB) (atom2493_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2494_nonneg g hg hA hB) (atom2495_nonneg g hg hA hB)) (add_nonneg (atom2496_nonneg g hg hA hB) (add_nonneg (atom2497_nonneg g hg hA hB) (atom2498_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2499_nonneg g hg hA hB) (atom2500_nonneg g hg hA hB)) (add_nonneg (atom2501_nonneg g hg hA hB) (add_nonneg (atom2502_nonneg g hg hA hB) (atom2503_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2504_nonneg g hg hA hB) (atom2505_nonneg g hg hA hB)) (add_nonneg (atom2506_nonneg g hg hA hB) (add_nonneg (atom2507_nonneg g hg hA hB) (atom2508_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2509_nonneg g hg hA hB) (atom2510_nonneg g hg hA hB)) (add_nonneg (atom2511_nonneg g hg hA hB) (add_nonneg (atom2512_nonneg g hg hA hB) (atom2513_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2514_nonneg g hg hA hB) (atom2515_nonneg g hg hA hB)) (add_nonneg (atom2516_nonneg g hg hA hB) (add_nonneg (atom2517_nonneg g hg hA hB) (atom2518_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2519_nonneg g hg hA hB) (atom2520_nonneg g hg hA hB)) (add_nonneg (atom2521_nonneg g hg hA hB) (add_nonneg (atom2522_nonneg g hg hA hB) (atom2523_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2524_nonneg g hg hA hB) (atom2525_nonneg g hg hA hB)) (add_nonneg (atom2526_nonneg g hg hA hB) (add_nonneg (atom2527_nonneg g hg hA hB) (atom2528_nonneg g hg hA hB))))))))

end APPT.Finite24
