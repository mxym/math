import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0449 : SparsePolynomial.Poly := [([0,13,19], 1)]
theorem eval_atom0449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0449 = ((g 0) * (g 13) * (g 19)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (280362100233600 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450 : SparsePolynomial.Poly := [([0,13,20], 1)]
theorem eval_atom0450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0450 = ((g 0) * (g 13) * (g 20)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283858818566400 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451 : SparsePolynomial.Poly := [([0,13,21], 1)]
theorem eval_atom0451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0451 = ((g 0) * (g 13) * (g 21)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220539543840000 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452 : SparsePolynomial.Poly := [([0,13,22], 1)]
theorem eval_atom0452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0452 = ((g 0) * (g 13) * (g 22)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165174808478400 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453 : SparsePolynomial.Poly := [([0,13,23], 1)]
theorem eval_atom0453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0453 = ((g 0) * (g 13) * (g 23)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153751952692800 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454 : SparsePolynomial.Poly := [([0,14,14], 1)]
theorem eval_atom0454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0454 = ((g 0) * (g 14) * (g 14)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180207265392000 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455 : SparsePolynomial.Poly := [([0,14,15], 1)]
theorem eval_atom0455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0455 = ((g 0) * (g 14) * (g 15)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (326270355747840 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456 : SparsePolynomial.Poly := [([0,14,16], 1)]
theorem eval_atom0456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0456 = ((g 0) * (g 14) * (g 16)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298937896306560 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457 : SparsePolynomial.Poly := [([0,14,17], 1)]
theorem eval_atom0457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0457 = ((g 0) * (g 14) * (g 17)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (297051845428800 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458 : SparsePolynomial.Poly := [([0,14,18], 1)]
theorem eval_atom0458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0458 = ((g 0) * (g 14) * (g 18)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320423596416000 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459 : SparsePolynomial.Poly := [([0,14,19], 1)]
theorem eval_atom0459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0459 = ((g 0) * (g 14) * (g 19)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262910161067400 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460 : SparsePolynomial.Poly := [([0,14,20], 1)]
theorem eval_atom0460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0460 = ((g 0) * (g 14) * (g 20)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266247131673600 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461 : SparsePolynomial.Poly := [([0,14,21], 1)]
theorem eval_atom0461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0461 = ((g 0) * (g 14) * (g 21)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203948449689600 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462 : SparsePolynomial.Poly := [([0,14,22], 1)]
theorem eval_atom0462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0462 = ((g 0) * (g 14) * (g 22)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163012699899000 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463 : SparsePolynomial.Poly := [([0,14,23], 1)]
theorem eval_atom0463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0463 = ((g 0) * (g 14) * (g 23)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150660684682200 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464 : SparsePolynomial.Poly := [([0,15,15], 1)]
theorem eval_atom0464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0464 = ((g 0) * (g 15) * (g 15)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185418634867200 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465 : SparsePolynomial.Poly := [([0,15,16], 1)]
theorem eval_atom0465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0465 = ((g 0) * (g 15) * (g 16)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (335715348810240 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466 : SparsePolynomial.Poly := [([0,15,17], 1)]
theorem eval_atom0466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0466 = ((g 0) * (g 15) * (g 17)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309666780864000 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467 : SparsePolynomial.Poly := [([0,15,18], 1)]
theorem eval_atom0467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0467 = ((g 0) * (g 15) * (g 18)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331449735052800 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468 : SparsePolynomial.Poly := [([0,15,19], 1)]
theorem eval_atom0468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0468 = ((g 0) * (g 15) * (g 19)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269855932147200 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469 : SparsePolynomial.Poly := [([0,15,20], 1)]
theorem eval_atom0469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0469 = ((g 0) * (g 15) * (g 20)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278367314803200 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470 : SparsePolynomial.Poly := [([0,15,21], 1)]
theorem eval_atom0470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0470 = ((g 0) * (g 15) * (g 21)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216773511897600 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471 : SparsePolynomial.Poly := [([0,15,22], 1)]
theorem eval_atom0471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0471 = ((g 0) * (g 15) * (g 22)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154848692880000 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472 : SparsePolynomial.Poly := [([0,15,23], 1)]
theorem eval_atom0472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0472 = ((g 0) * (g 15) * (g 23)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139633710451200 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473 : SparsePolynomial.Poly := [([0,16,16], 1)]
theorem eval_atom0473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0473 = ((g 0) * (g 16) * (g 16)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190423018598400 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474 : SparsePolynomial.Poly := [([0,16,17], 1)]
theorem eval_atom0474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0474 = ((g 0) * (g 16) * (g 17)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337110459571200 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475 : SparsePolynomial.Poly := [([0,16,18], 1)]
theorem eval_atom0475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0475 = ((g 0) * (g 16) * (g 18)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (339520246128000 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476 : SparsePolynomial.Poly := [([0,16,19], 1)]
theorem eval_atom0476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0476 = ((g 0) * (g 16) * (g 19)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272720067177600 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477 : SparsePolynomial.Poly := [([0,16,20], 1)]
theorem eval_atom0477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0477 = ((g 0) * (g 16) * (g 20)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269798105001600 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478 : SparsePolynomial.Poly := [([0,16,21], 1)]
theorem eval_atom0478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0478 = ((g 0) * (g 16) * (g 21)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202997926051200 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479 : SparsePolynomial.Poly := [([0,16,22], 1)]
theorem eval_atom0479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0479 = ((g 0) * (g 16) * (g 22)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129247858454400 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480 : SparsePolynomial.Poly := [([0,16,23], 1)]
theorem eval_atom0480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0480 = ((g 0) * (g 16) * (g 23)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121733228937600 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481 : SparsePolynomial.Poly := [([0,17,17], 1)]
theorem eval_atom0481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0481 = ((g 0) * (g 17) * (g 17)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187597703462400 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482 : SparsePolynomial.Poly := [([0,17,18], 1)]
theorem eval_atom0482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0482 = ((g 0) * (g 17) * (g 18)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350073941817600 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483 : SparsePolynomial.Poly := [([0,17,19], 1)]
theorem eval_atom0483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0483 = ((g 0) * (g 17) * (g 19)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283033756051200 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484 : SparsePolynomial.Poly := [([0,17,20], 1)]
theorem eval_atom0484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0484 = ((g 0) * (g 17) * (g 20)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278611187500800 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485 : SparsePolynomial.Poly := [([0,17,21], 1)]
theorem eval_atom0485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0485 = ((g 0) * (g 17) * (g 21)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211571001734400 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486 : SparsePolynomial.Poly := [([0,17,22], 1)]
theorem eval_atom0486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0486 = ((g 0) * (g 17) * (g 22)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135196644844800 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487 : SparsePolynomial.Poly := [([0,17,23], 1)]
theorem eval_atom0487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0487 = ((g 0) * (g 17) * (g 23)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126181408953600 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488 : SparsePolynomial.Poly := [([0,18,18], 1)]
theorem eval_atom0488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0488 = ((g 0) * (g 18) * (g 18)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194082719846400 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489 : SparsePolynomial.Poly := [([0,18,19], 1)]
theorem eval_atom0489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0489 = ((g 0) * (g 18) * (g 19)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329949128678400 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490 : SparsePolynomial.Poly := [([0,18,20], 1)]
theorem eval_atom0490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0490 = ((g 0) * (g 18) * (g 20)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342153716889600 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491 : SparsePolynomial.Poly := [([0,18,21], 1)]
theorem eval_atom0491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0491 = ((g 0) * (g 18) * (g 21)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283937405875200 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492 : SparsePolynomial.Poly := [([0,18,22], 1)]
theorem eval_atom0492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0492 = ((g 0) * (g 18) * (g 22)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163805135155200 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493 : SparsePolynomial.Poly := [([0,18,23], 1)]
theorem eval_atom0493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0493 = ((g 0) * (g 18) * (g 23)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171417056025600 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494 : SparsePolynomial.Poly := [([0,19,19], 1)]
theorem eval_atom0494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0494 = ((g 0) * (g 19) * (g 19)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137682213419520 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495 : SparsePolynomial.Poly := [([0,19,20], 1)]
theorem eval_atom0495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 0) * (g 19) * (g 20)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278791917465600 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496 : SparsePolynomial.Poly := [([0,19,21], 1)]
theorem eval_atom0496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 0) * (g 19) * (g 21)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292017098419200 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497 : SparsePolynomial.Poly := [([0,19,22], 1)]
theorem eval_atom0497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 0) * (g 19) * (g 22)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172905420441600 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498 : SparsePolynomial.Poly := [([0,19,23], 1)]
theorem eval_atom0498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 0) * (g 19) * (g 23)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181537934054400 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499 : SparsePolynomial.Poly := [([0,20,20], 1)]
theorem eval_atom0499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 0) * (g 20) * (g 20)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142925508633600 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500 : SparsePolynomial.Poly := [([0,20,21], 1)]
theorem eval_atom0500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 0) * (g 20) * (g 21)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (300096790963200 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501 : SparsePolynomial.Poly := [([0,20,22], 1)]
theorem eval_atom0501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 0) * (g 20) * (g 22)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182005705728000 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502 : SparsePolynomial.Poly := [([0,20,23], 1)]
theorem eval_atom0502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 0) * (g 20) * (g 23)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167207110963200 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503 : SparsePolynomial.Poly := [([0,21,21], 1)]
theorem eval_atom0503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 0) * (g 21) * (g 21)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154088241753600 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504 : SparsePolynomial.Poly := [([0,21,22], 1)]
theorem eval_atom0504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 0) * (g 21) * (g 22)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191105991014400 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505 : SparsePolynomial.Poly := [([0,21,23], 1)]
theorem eval_atom0505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 0) * (g 21) * (g 23)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177327988992000 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506 : SparsePolynomial.Poly := [([0,22,22], 1)]
theorem eval_atom0506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 0) * (g 22) * (g 22)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22316002884000 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507 : SparsePolynomial.Poly := [([0,22,23], 1)]
theorem eval_atom0507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 0) * (g 22) * (g 23)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35848320076800 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43587815040000 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38442326630400 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33296838220800 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511 : SparsePolynomial.Poly := [([1,1,5], 1)]
theorem eval_atom0511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35034243552000 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23005861401600 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513 : SparsePolynomial.Poly := [([1,1,7], 1)]
theorem eval_atom0513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 1) * (g 1) * (g 7)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17860372992000 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514 : SparsePolynomial.Poly := [([1,1,8], 1)]
theorem eval_atom0514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 1) * (g 1) * (g 8)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12714884582400 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515 : SparsePolynomial.Poly := [([1,1,9], 1)]
theorem eval_atom0515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13581177218928 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516 : SparsePolynomial.Poly := [([1,1,10], 1)]
theorem eval_atom0516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 1) * (g 1) * (g 10)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26079185843568 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517 : SparsePolynomial.Poly := [([1,1,11], 1)]
theorem eval_atom0517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 1) * (g 1) * (g 11)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36938767228704 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518 : SparsePolynomial.Poly := [([1,1,12], 1)]
theorem eval_atom0518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 1) * (g 1) * (g 12)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59715261042624 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519 : SparsePolynomial.Poly := [([1,1,13], 1)]
theorem eval_atom0519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 1) * (g 1) * (g 13)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45908642102400 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520 : SparsePolynomial.Poly := [([1,1,14], 1)]
theorem eval_atom0520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 1) * (g 1) * (g 14)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28427760345600 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521 : SparsePolynomial.Poly := [([1,1,15], 1)]
theorem eval_atom0521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 1) * (g 1) * (g 15)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25733885184000 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522 : SparsePolynomial.Poly := [([1,1,16], 1)]
theorem eval_atom0522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 1) * (g 1) * (g 16)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11217499776000 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523 : SparsePolynomial.Poly := [([1,1,17], 1)]
theorem eval_atom0523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 1) * (g 1) * (g 17)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6633852825600 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524 : SparsePolynomial.Poly := [([1,1,18], 1)]
theorem eval_atom0524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 1) * (g 1) * (g 18)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29512140134400 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525 : SparsePolynomial.Poly := [([1,1,20], 1)]
theorem eval_atom0525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 1) * (g 1) * (g 20)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6208605849600 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 1) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85347068083200 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162444344832000 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154194553497600 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block008 : SparsePolynomial.Poly := [([0,13,19], 280362100233600), ([0,13,20], 283858818566400), ([0,13,21], 220539543840000), ([0,13,22], 165174808478400), ([0,13,23], 153751952692800), ([0,14,14], 180207265392000), ([0,14,15], 326270355747840), ([0,14,16], 298937896306560), ([0,14,17], 297051845428800), ([0,14,18], 320423596416000), ([0,14,19], 262910161067400), ([0,14,20], 266247131673600), ([0,14,21], 203948449689600), ([0,14,22], 163012699899000), ([0,14,23], 150660684682200), ([0,15,15], 185418634867200), ([0,15,16], 335715348810240), ([0,15,17], 309666780864000), ([0,15,18], 331449735052800), ([0,15,19], 269855932147200), ([0,15,20], 278367314803200), ([0,15,21], 216773511897600), ([0,15,22], 154848692880000), ([0,15,23], 139633710451200), ([0,16,16], 190423018598400), ([0,16,17], 337110459571200), ([0,16,18], 339520246128000), ([0,16,19], 272720067177600), ([0,16,20], 269798105001600), ([0,16,21], 202997926051200), ([0,16,22], 129247858454400), ([0,16,23], 121733228937600), ([0,17,17], 187597703462400), ([0,17,18], 350073941817600), ([0,17,19], 283033756051200), ([0,17,20], 278611187500800), ([0,17,21], 211571001734400), ([0,17,22], 135196644844800), ([0,17,23], 126181408953600), ([0,18,18], 194082719846400), ([0,18,19], 329949128678400), ([0,18,20], 342153716889600), ([0,18,21], 283937405875200), ([0,18,22], 163805135155200), ([0,18,23], 171417056025600), ([0,19,19], 137682213419520), ([0,19,20], 278791917465600), ([0,19,21], 292017098419200), ([0,19,22], 172905420441600), ([0,19,23], 181537934054400), ([0,20,20], 142925508633600), ([0,20,21], 300096790963200), ([0,20,22], 182005705728000), ([0,20,23], 167207110963200), ([0,21,21], 154088241753600), ([0,21,22], 191105991014400), ([0,21,23], 177327988992000), ([0,22,22], 22316002884000), ([0,22,23], 35848320076800), ([1,1,2], 43587815040000), ([1,1,3], 38442326630400), ([1,1,4], 33296838220800), ([1,1,5], 35034243552000), ([1,1,6], 23005861401600), ([1,1,7], 17860372992000), ([1,1,8], 12714884582400), ([1,1,9], 13581177218928), ([1,1,10], 26079185843568), ([1,1,11], 36938767228704), ([1,1,12], 59715261042624), ([1,1,13], 45908642102400), ([1,1,14], 28427760345600), ([1,1,15], 25733885184000), ([1,1,16], 11217499776000), ([1,1,17], 6633852825600), ([1,1,18], 29512140134400), ([1,1,20], 6208605849600), ([1,2,2], 85347068083200), ([1,2,3], 162444344832000), ([1,2,4], 154194553497600)]
theorem block008_data : block008 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (280362100233600 : Int) atom0449) (SparsePolynomial.scale (283858818566400 : Int) atom0450)) (SparsePolynomial.merge (SparsePolynomial.scale (220539543840000 : Int) atom0451) (SparsePolynomial.merge (SparsePolynomial.scale (165174808478400 : Int) atom0452) (SparsePolynomial.scale (153751952692800 : Int) atom0453)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (180207265392000 : Int) atom0454) (SparsePolynomial.scale (326270355747840 : Int) atom0455)) (SparsePolynomial.merge (SparsePolynomial.scale (298937896306560 : Int) atom0456) (SparsePolynomial.merge (SparsePolynomial.scale (297051845428800 : Int) atom0457) (SparsePolynomial.scale (320423596416000 : Int) atom0458))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (262910161067400 : Int) atom0459) (SparsePolynomial.scale (266247131673600 : Int) atom0460)) (SparsePolynomial.merge (SparsePolynomial.scale (203948449689600 : Int) atom0461) (SparsePolynomial.merge (SparsePolynomial.scale (163012699899000 : Int) atom0462) (SparsePolynomial.scale (150660684682200 : Int) atom0463)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (185418634867200 : Int) atom0464) (SparsePolynomial.scale (335715348810240 : Int) atom0465)) (SparsePolynomial.merge (SparsePolynomial.scale (309666780864000 : Int) atom0466) (SparsePolynomial.merge (SparsePolynomial.scale (331449735052800 : Int) atom0467) (SparsePolynomial.scale (269855932147200 : Int) atom0468)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (278367314803200 : Int) atom0469) (SparsePolynomial.scale (216773511897600 : Int) atom0470)) (SparsePolynomial.merge (SparsePolynomial.scale (154848692880000 : Int) atom0471) (SparsePolynomial.merge (SparsePolynomial.scale (139633710451200 : Int) atom0472) (SparsePolynomial.scale (190423018598400 : Int) atom0473)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (337110459571200 : Int) atom0474) (SparsePolynomial.scale (339520246128000 : Int) atom0475)) (SparsePolynomial.merge (SparsePolynomial.scale (272720067177600 : Int) atom0476) (SparsePolynomial.merge (SparsePolynomial.scale (269798105001600 : Int) atom0477) (SparsePolynomial.scale (202997926051200 : Int) atom0478))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (129247858454400 : Int) atom0479) (SparsePolynomial.scale (121733228937600 : Int) atom0480)) (SparsePolynomial.merge (SparsePolynomial.scale (187597703462400 : Int) atom0481) (SparsePolynomial.merge (SparsePolynomial.scale (350073941817600 : Int) atom0482) (SparsePolynomial.scale (283033756051200 : Int) atom0483)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (278611187500800 : Int) atom0484) (SparsePolynomial.scale (211571001734400 : Int) atom0485)) (SparsePolynomial.merge (SparsePolynomial.scale (135196644844800 : Int) atom0486) (SparsePolynomial.merge (SparsePolynomial.scale (126181408953600 : Int) atom0487) (SparsePolynomial.scale (194082719846400 : Int) atom0488))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (329949128678400 : Int) atom0489) (SparsePolynomial.scale (342153716889600 : Int) atom0490)) (SparsePolynomial.merge (SparsePolynomial.scale (283937405875200 : Int) atom0491) (SparsePolynomial.merge (SparsePolynomial.scale (163805135155200 : Int) atom0492) (SparsePolynomial.scale (171417056025600 : Int) atom0493)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (137682213419520 : Int) atom0494) (SparsePolynomial.scale (278791917465600 : Int) atom0495)) (SparsePolynomial.merge (SparsePolynomial.scale (292017098419200 : Int) atom0496) (SparsePolynomial.merge (SparsePolynomial.scale (172905420441600 : Int) atom0497) (SparsePolynomial.scale (181537934054400 : Int) atom0498))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142925508633600 : Int) atom0499) (SparsePolynomial.scale (300096790963200 : Int) atom0500)) (SparsePolynomial.merge (SparsePolynomial.scale (182005705728000 : Int) atom0501) (SparsePolynomial.merge (SparsePolynomial.scale (167207110963200 : Int) atom0502) (SparsePolynomial.scale (154088241753600 : Int) atom0503)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (191105991014400 : Int) atom0504) (SparsePolynomial.scale (177327988992000 : Int) atom0505)) (SparsePolynomial.merge (SparsePolynomial.scale (22316002884000 : Int) atom0506) (SparsePolynomial.merge (SparsePolynomial.scale (35848320076800 : Int) atom0507) (SparsePolynomial.scale (43587815040000 : Int) atom0508)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38442326630400 : Int) atom0509) (SparsePolynomial.scale (33296838220800 : Int) atom0510)) (SparsePolynomial.merge (SparsePolynomial.scale (35034243552000 : Int) atom0511) (SparsePolynomial.merge (SparsePolynomial.scale (23005861401600 : Int) atom0512) (SparsePolynomial.scale (17860372992000 : Int) atom0513)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12714884582400 : Int) atom0514) (SparsePolynomial.scale (13581177218928 : Int) atom0515)) (SparsePolynomial.merge (SparsePolynomial.scale (26079185843568 : Int) atom0516) (SparsePolynomial.merge (SparsePolynomial.scale (36938767228704 : Int) atom0517) (SparsePolynomial.scale (59715261042624 : Int) atom0518))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (45908642102400 : Int) atom0519) (SparsePolynomial.scale (28427760345600 : Int) atom0520)) (SparsePolynomial.merge (SparsePolynomial.scale (25733885184000 : Int) atom0521) (SparsePolynomial.merge (SparsePolynomial.scale (11217499776000 : Int) atom0522) (SparsePolynomial.scale (6633852825600 : Int) atom0523)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (29512140134400 : Int) atom0524) (SparsePolynomial.scale (6208605849600 : Int) atom0525)) (SparsePolynomial.merge (SparsePolynomial.scale (85347068083200 : Int) atom0526) (SparsePolynomial.merge (SparsePolynomial.scale (162444344832000 : Int) atom0527) (SparsePolynomial.scale (154194553497600 : Int) atom0528)))))))) := by decide +kernel
theorem block008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block008 := by
  rw [block008_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0449_nonneg g hg hA hB) (atom0450_nonneg g hg hA hB)) (add_nonneg (atom0451_nonneg g hg hA hB) (add_nonneg (atom0452_nonneg g hg hA hB) (atom0453_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0454_nonneg g hg hA hB) (atom0455_nonneg g hg hA hB)) (add_nonneg (atom0456_nonneg g hg hA hB) (add_nonneg (atom0457_nonneg g hg hA hB) (atom0458_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0459_nonneg g hg hA hB) (atom0460_nonneg g hg hA hB)) (add_nonneg (atom0461_nonneg g hg hA hB) (add_nonneg (atom0462_nonneg g hg hA hB) (atom0463_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0464_nonneg g hg hA hB) (atom0465_nonneg g hg hA hB)) (add_nonneg (atom0466_nonneg g hg hA hB) (add_nonneg (atom0467_nonneg g hg hA hB) (atom0468_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0469_nonneg g hg hA hB) (atom0470_nonneg g hg hA hB)) (add_nonneg (atom0471_nonneg g hg hA hB) (add_nonneg (atom0472_nonneg g hg hA hB) (atom0473_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0474_nonneg g hg hA hB) (atom0475_nonneg g hg hA hB)) (add_nonneg (atom0476_nonneg g hg hA hB) (add_nonneg (atom0477_nonneg g hg hA hB) (atom0478_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0479_nonneg g hg hA hB) (atom0480_nonneg g hg hA hB)) (add_nonneg (atom0481_nonneg g hg hA hB) (add_nonneg (atom0482_nonneg g hg hA hB) (atom0483_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0484_nonneg g hg hA hB) (atom0485_nonneg g hg hA hB)) (add_nonneg (atom0486_nonneg g hg hA hB) (add_nonneg (atom0487_nonneg g hg hA hB) (atom0488_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0489_nonneg g hg hA hB) (atom0490_nonneg g hg hA hB)) (add_nonneg (atom0491_nonneg g hg hA hB) (add_nonneg (atom0492_nonneg g hg hA hB) (atom0493_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0494_nonneg g hg hA hB) (atom0495_nonneg g hg hA hB)) (add_nonneg (atom0496_nonneg g hg hA hB) (add_nonneg (atom0497_nonneg g hg hA hB) (atom0498_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0499_nonneg g hg hA hB) (atom0500_nonneg g hg hA hB)) (add_nonneg (atom0501_nonneg g hg hA hB) (add_nonneg (atom0502_nonneg g hg hA hB) (atom0503_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0504_nonneg g hg hA hB) (atom0505_nonneg g hg hA hB)) (add_nonneg (atom0506_nonneg g hg hA hB) (add_nonneg (atom0507_nonneg g hg hA hB) (atom0508_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0509_nonneg g hg hA hB) (atom0510_nonneg g hg hA hB)) (add_nonneg (atom0511_nonneg g hg hA hB) (add_nonneg (atom0512_nonneg g hg hA hB) (atom0513_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0514_nonneg g hg hA hB) (atom0515_nonneg g hg hA hB)) (add_nonneg (atom0516_nonneg g hg hA hB) (add_nonneg (atom0517_nonneg g hg hA hB) (atom0518_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0519_nonneg g hg hA hB) (atom0520_nonneg g hg hA hB)) (add_nonneg (atom0521_nonneg g hg hA hB) (add_nonneg (atom0522_nonneg g hg hA hB) (atom0523_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0524_nonneg g hg hA hB) (atom0525_nonneg g hg hA hB)) (add_nonneg (atom0526_nonneg g hg hA hB) (add_nonneg (atom0527_nonneg g hg hA hB) (atom0528_nonneg g hg hA hB))))))))

end APPT.Finite24
