import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0736 : SparsePolynomial.Poly := [([2,14,18], 1)]
theorem eval_atom0736 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 2) * (g 14) * (g 18)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51478079385600 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737 : SparsePolynomial.Poly := [([2,14,19], 1)]
theorem eval_atom0737 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 2) * (g 14) * (g 19)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39762525196800 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738 : SparsePolynomial.Poly := [([2,14,20], 1)]
theorem eval_atom0738 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 2) * (g 14) * (g 20)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56627433676800 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739 : SparsePolynomial.Poly := [([2,15,15], 1)]
theorem eval_atom0739 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33575181696000 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740 : SparsePolynomial.Poly := [([2,15,16], 1)]
theorem eval_atom0740 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55106209267200 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741 : SparsePolynomial.Poly := [([2,15,17], 1)]
theorem eval_atom0741 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75090472934400 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742 : SparsePolynomial.Poly := [([2,15,18], 1)]
theorem eval_atom0742 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 2) * (g 15) * (g 18)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65114976729600 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743 : SparsePolynomial.Poly := [([2,15,19], 1)]
theorem eval_atom0743 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 2) * (g 15) * (g 19)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39869803411200 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744 : SparsePolynomial.Poly := [([2,15,20], 1)]
theorem eval_atom0744 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 2) * (g 15) * (g 20)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60710287881600 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745 : SparsePolynomial.Poly := [([2,16,16], 1)]
theorem eval_atom0745 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22698910402560 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746 : SparsePolynomial.Poly := [([2,16,17], 1)]
theorem eval_atom0746 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61504901337600 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747 : SparsePolynomial.Poly := [([2,16,18], 1)]
theorem eval_atom0747 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 2) * (g 16) * (g 18)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60041007129600 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748 : SparsePolynomial.Poly := [([2,16,19], 1)]
theorem eval_atom0748 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 2) * (g 16) * (g 19)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39977081625600 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749 : SparsePolynomial.Poly := [([2,16,20], 1)]
theorem eval_atom0749 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 2) * (g 16) * (g 20)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47368164009600 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750 : SparsePolynomial.Poly := [([2,17,17], 1)]
theorem eval_atom0750 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39973873766400 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751 : SparsePolynomial.Poly := [([2,17,18], 1)]
theorem eval_atom0751 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 2) * (g 17) * (g 18)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61939813017600 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752 : SparsePolynomial.Poly := [([2,17,19], 1)]
theorem eval_atom0752 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 2) * (g 17) * (g 19)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39050030880000 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753 : SparsePolynomial.Poly := [([2,17,20], 1)]
theorem eval_atom0753 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 2) * (g 17) * (g 20)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49287368592000 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754 : SparsePolynomial.Poly := [([2,18,18], 1)]
theorem eval_atom0754 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 2) * (g 18) * (g 18)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20684399500800 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755 : SparsePolynomial.Poly := [([2,18,19], 1)]
theorem eval_atom0755 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 2) * (g 18) * (g 19)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25066859529600 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756 : SparsePolynomial.Poly := [([2,18,20], 1)]
theorem eval_atom0756 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 2) * (g 18) * (g 20)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36979573680000 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757 : SparsePolynomial.Poly := [([2,19,19], 1)]
theorem eval_atom0757 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 2) * (g 19) * (g 19)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1177160947200 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758 : SparsePolynomial.Poly := [([2,19,20], 1)]
theorem eval_atom0758 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 2) * (g 19) * (g 20)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14227652376000 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759 : SparsePolynomial.Poly := [([2,20,20], 1)]
theorem eval_atom0759 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 2) * (g 20) * (g 20)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11225070460800 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0760 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2137832524800 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0761 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5713773004800 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0762 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6505426397952 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0763 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6259026816000 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0764 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7013098571904 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0765 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6815549260800 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom0766 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6543004608000 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767 : SparsePolynomial.Poly := [([3,3,10], 1)]
theorem eval_atom0767 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6270459955200 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768 : SparsePolynomial.Poly := [([3,3,11], 1)]
theorem eval_atom0768 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5685991718400 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769 : SparsePolynomial.Poly := [([3,3,12], 1)]
theorem eval_atom0769 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3051970342400 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770 : SparsePolynomial.Poly := [([3,3,13], 1)]
theorem eval_atom0770 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0770 = ((g 3) * (g 3) * (g 13)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0770_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2161027814400 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771 : SparsePolynomial.Poly := [([3,3,14], 1)]
theorem eval_atom0771 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0771 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0771_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2147497228800 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772 : SparsePolynomial.Poly := [([3,3,15], 1)]
theorem eval_atom0772 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0772 = ((g 3) * (g 3) * (g 15)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0772_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6541071667200 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773 : SparsePolynomial.Poly := [([3,3,17], 1)]
theorem eval_atom0773 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0773 = ((g 3) * (g 3) * (g 17)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0773_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4107293568000 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0774 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0774 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0774_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5453792467200 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0775 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0775 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0775_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8897326502400 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0776 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0776 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0776_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9046491955200 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0777 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0777 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0777_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11227298865408 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0778 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11504863641600 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom0779 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0779 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0779_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11632437734400 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom0780 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0780 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0780_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11760011827200 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom0781 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0781 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0781_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11263738752000 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom0782 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0782 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0782_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7479371244800 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom0783 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0783 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0783_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7015608633600 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom0784 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0784 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0784_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7429257964800 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785 : SparsePolynomial.Poly := [([3,4,15], 1)]
theorem eval_atom0785 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0785 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0785_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15664552243200 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786 : SparsePolynomial.Poly := [([3,4,16], 1)]
theorem eval_atom0786 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0786 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0786_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6941794456800 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787 : SparsePolynomial.Poly := [([3,4,17], 1)]
theorem eval_atom0787 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0787 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0787_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12142322841600 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788 : SparsePolynomial.Poly := [([3,4,18], 1)]
theorem eval_atom0788 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 3) * (g 4) * (g 18)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9407502064800 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789 : SparsePolynomial.Poly := [([3,4,19], 1)]
theorem eval_atom0789 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0789 = ((g 3) * (g 4) * (g 19)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0789_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10908913831200 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790 : SparsePolynomial.Poly := [([3,4,20], 1)]
theorem eval_atom0790 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0790 = ((g 3) * (g 4) * (g 20)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0790_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12410325597600 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0791 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0791 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0791_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8572592448000 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0792 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0792 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0792_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15532145798400 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0793 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0793 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0793_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12347854101504 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0794 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0794 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0794_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12361384687104 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom0795 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0795 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0795_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13891307330304 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom0796 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0796 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0796_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13961859669504 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom0797 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14138249992704 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798 : SparsePolynomial.Poly := [([3,5,12], 1)]
theorem eval_atom0798 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0798 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0798_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11604495183104 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799 : SparsePolynomial.Poly := [([3,5,13], 1)]
theorem eval_atom0799 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0799 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0799_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11137833160704 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800 : SparsePolynomial.Poly := [([3,5,14], 1)]
theorem eval_atom0800 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0800 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0800_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11810496559104 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801 : SparsePolynomial.Poly := [([3,5,15], 1)]
theorem eval_atom0801 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0801 = ((g 3) * (g 5) * (g 15)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0801_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21229717077504 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802 : SparsePolynomial.Poly := [([3,5,16], 1)]
theorem eval_atom0802 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0802 = ((g 3) * (g 5) * (g 16)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0802_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12805392234240 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803 : SparsePolynomial.Poly := [([3,5,17], 1)]
theorem eval_atom0803 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0803 = ((g 3) * (g 5) * (g 17)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0803_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19052814472704 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804 : SparsePolynomial.Poly := [([3,5,18], 1)]
theorem eval_atom0804 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0804 = ((g 3) * (g 5) * (g 18)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0804_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17717790074112 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805 : SparsePolynomial.Poly := [([3,5,19], 1)]
theorem eval_atom0805 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 3) * (g 5) * (g 19)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20763990639360 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806 : SparsePolynomial.Poly := [([3,5,20], 1)]
theorem eval_atom0806 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0806 = ((g 3) * (g 5) * (g 20)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0806_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23810191204608 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0807 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0807 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0807_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12088611763200 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0808 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0808 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0808_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21174628264704 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0809 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0809 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0809_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391473769600 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810 : SparsePolynomial.Poly := [([3,6,9], 1)]
theorem eval_atom0810 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0810 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0810_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14851113177600 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811 : SparsePolynomial.Poly := [([3,6,10], 1)]
theorem eval_atom0811 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0811 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0811_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15271527801600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812 : SparsePolynomial.Poly := [([3,6,11], 1)]
theorem eval_atom0812 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15121004774400 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813 : SparsePolynomial.Poly := [([3,6,12], 1)]
theorem eval_atom0813 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0813 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0813_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13264025600000 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814 : SparsePolynomial.Poly := [([3,6,13], 1)]
theorem eval_atom0814 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0814 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0814_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13150125273600 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0815 : SparsePolynomial.Poly := [([3,6,14], 1)]
theorem eval_atom0815 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0815 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0815_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13913636889600 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block011 : SparsePolynomial.Poly := [([2,14,18], 51478079385600), ([2,14,19], 39762525196800), ([2,14,20], 56627433676800), ([2,15,15], 33575181696000), ([2,15,16], 55106209267200), ([2,15,17], 75090472934400), ([2,15,18], 65114976729600), ([2,15,19], 39869803411200), ([2,15,20], 60710287881600), ([2,16,16], 22698910402560), ([2,16,17], 61504901337600), ([2,16,18], 60041007129600), ([2,16,19], 39977081625600), ([2,16,20], 47368164009600), ([2,17,17], 39973873766400), ([2,17,18], 61939813017600), ([2,17,19], 39050030880000), ([2,17,20], 49287368592000), ([2,18,18], 20684399500800), ([2,18,19], 25066859529600), ([2,18,20], 36979573680000), ([2,19,19], 1177160947200), ([2,19,20], 14227652376000), ([2,20,20], 11225070460800), ([3,3,3], 2137832524800), ([3,3,4], 5713773004800), ([3,3,5], 6505426397952), ([3,3,6], 6259026816000), ([3,3,7], 7013098571904), ([3,3,8], 6815549260800), ([3,3,9], 6543004608000), ([3,3,10], 6270459955200), ([3,3,11], 5685991718400), ([3,3,12], 3051970342400), ([3,3,13], 2161027814400), ([3,3,14], 2147497228800), ([3,3,15], 6541071667200), ([3,3,17], 4107293568000), ([3,4,4], 5453792467200), ([3,4,5], 8897326502400), ([3,4,6], 9046491955200), ([3,4,7], 11227298865408), ([3,4,8], 11504863641600), ([3,4,9], 11632437734400), ([3,4,10], 11760011827200), ([3,4,11], 11263738752000), ([3,4,12], 7479371244800), ([3,4,13], 7015608633600), ([3,4,14], 7429257964800), ([3,4,15], 15664552243200), ([3,4,16], 6941794456800), ([3,4,17], 12142322841600), ([3,4,18], 9407502064800), ([3,4,19], 10908913831200), ([3,4,20], 12410325597600), ([3,5,5], 8572592448000), ([3,5,6], 15532145798400), ([3,5,7], 12347854101504), ([3,5,8], 12361384687104), ([3,5,9], 13891307330304), ([3,5,10], 13961859669504), ([3,5,11], 14138249992704), ([3,5,12], 11604495183104), ([3,5,13], 11137833160704), ([3,5,14], 11810496559104), ([3,5,15], 21229717077504), ([3,5,16], 12805392234240), ([3,5,17], 19052814472704), ([3,5,18], 17717790074112), ([3,5,19], 20763990639360), ([3,5,20], 23810191204608), ([3,6,6], 12088611763200), ([3,6,7], 21174628264704), ([3,6,8], 17391473769600), ([3,6,9], 14851113177600), ([3,6,10], 15271527801600), ([3,6,11], 15121004774400), ([3,6,12], 13264025600000), ([3,6,13], 13150125273600), ([3,6,14], 13913636889600)]
theorem block011_data : block011 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (51478079385600 : Int) atom0736) (SparsePolynomial.scale (39762525196800 : Int) atom0737)) (SparsePolynomial.merge (SparsePolynomial.scale (56627433676800 : Int) atom0738) (SparsePolynomial.merge (SparsePolynomial.scale (33575181696000 : Int) atom0739) (SparsePolynomial.scale (55106209267200 : Int) atom0740)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (75090472934400 : Int) atom0741) (SparsePolynomial.scale (65114976729600 : Int) atom0742)) (SparsePolynomial.merge (SparsePolynomial.scale (39869803411200 : Int) atom0743) (SparsePolynomial.merge (SparsePolynomial.scale (60710287881600 : Int) atom0744) (SparsePolynomial.scale (22698910402560 : Int) atom0745))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61504901337600 : Int) atom0746) (SparsePolynomial.scale (60041007129600 : Int) atom0747)) (SparsePolynomial.merge (SparsePolynomial.scale (39977081625600 : Int) atom0748) (SparsePolynomial.merge (SparsePolynomial.scale (47368164009600 : Int) atom0749) (SparsePolynomial.scale (39973873766400 : Int) atom0750)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61939813017600 : Int) atom0751) (SparsePolynomial.scale (39050030880000 : Int) atom0752)) (SparsePolynomial.merge (SparsePolynomial.scale (49287368592000 : Int) atom0753) (SparsePolynomial.merge (SparsePolynomial.scale (20684399500800 : Int) atom0754) (SparsePolynomial.scale (25066859529600 : Int) atom0755)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36979573680000 : Int) atom0756) (SparsePolynomial.scale (1177160947200 : Int) atom0757)) (SparsePolynomial.merge (SparsePolynomial.scale (14227652376000 : Int) atom0758) (SparsePolynomial.merge (SparsePolynomial.scale (11225070460800 : Int) atom0759) (SparsePolynomial.scale (2137832524800 : Int) atom0760)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5713773004800 : Int) atom0761) (SparsePolynomial.scale (6505426397952 : Int) atom0762)) (SparsePolynomial.merge (SparsePolynomial.scale (6259026816000 : Int) atom0763) (SparsePolynomial.merge (SparsePolynomial.scale (7013098571904 : Int) atom0764) (SparsePolynomial.scale (6815549260800 : Int) atom0765))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6543004608000 : Int) atom0766) (SparsePolynomial.scale (6270459955200 : Int) atom0767)) (SparsePolynomial.merge (SparsePolynomial.scale (5685991718400 : Int) atom0768) (SparsePolynomial.merge (SparsePolynomial.scale (3051970342400 : Int) atom0769) (SparsePolynomial.scale (2161027814400 : Int) atom0770)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2147497228800 : Int) atom0771) (SparsePolynomial.scale (6541071667200 : Int) atom0772)) (SparsePolynomial.merge (SparsePolynomial.scale (4107293568000 : Int) atom0773) (SparsePolynomial.merge (SparsePolynomial.scale (5453792467200 : Int) atom0774) (SparsePolynomial.scale (8897326502400 : Int) atom0775))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9046491955200 : Int) atom0776) (SparsePolynomial.scale (11227298865408 : Int) atom0777)) (SparsePolynomial.merge (SparsePolynomial.scale (11504863641600 : Int) atom0778) (SparsePolynomial.merge (SparsePolynomial.scale (11632437734400 : Int) atom0779) (SparsePolynomial.scale (11760011827200 : Int) atom0780)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11263738752000 : Int) atom0781) (SparsePolynomial.scale (7479371244800 : Int) atom0782)) (SparsePolynomial.merge (SparsePolynomial.scale (7015608633600 : Int) atom0783) (SparsePolynomial.merge (SparsePolynomial.scale (7429257964800 : Int) atom0784) (SparsePolynomial.scale (15664552243200 : Int) atom0785))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6941794456800 : Int) atom0786) (SparsePolynomial.scale (12142322841600 : Int) atom0787)) (SparsePolynomial.merge (SparsePolynomial.scale (9407502064800 : Int) atom0788) (SparsePolynomial.merge (SparsePolynomial.scale (10908913831200 : Int) atom0789) (SparsePolynomial.scale (12410325597600 : Int) atom0790)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8572592448000 : Int) atom0791) (SparsePolynomial.scale (15532145798400 : Int) atom0792)) (SparsePolynomial.merge (SparsePolynomial.scale (12347854101504 : Int) atom0793) (SparsePolynomial.merge (SparsePolynomial.scale (12361384687104 : Int) atom0794) (SparsePolynomial.scale (13891307330304 : Int) atom0795)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13961859669504 : Int) atom0796) (SparsePolynomial.scale (14138249992704 : Int) atom0797)) (SparsePolynomial.merge (SparsePolynomial.scale (11604495183104 : Int) atom0798) (SparsePolynomial.merge (SparsePolynomial.scale (11137833160704 : Int) atom0799) (SparsePolynomial.scale (11810496559104 : Int) atom0800)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21229717077504 : Int) atom0801) (SparsePolynomial.scale (12805392234240 : Int) atom0802)) (SparsePolynomial.merge (SparsePolynomial.scale (19052814472704 : Int) atom0803) (SparsePolynomial.merge (SparsePolynomial.scale (17717790074112 : Int) atom0804) (SparsePolynomial.scale (20763990639360 : Int) atom0805))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23810191204608 : Int) atom0806) (SparsePolynomial.scale (12088611763200 : Int) atom0807)) (SparsePolynomial.merge (SparsePolynomial.scale (21174628264704 : Int) atom0808) (SparsePolynomial.merge (SparsePolynomial.scale (17391473769600 : Int) atom0809) (SparsePolynomial.scale (14851113177600 : Int) atom0810)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15271527801600 : Int) atom0811) (SparsePolynomial.scale (15121004774400 : Int) atom0812)) (SparsePolynomial.merge (SparsePolynomial.scale (13264025600000 : Int) atom0813) (SparsePolynomial.merge (SparsePolynomial.scale (13150125273600 : Int) atom0814) (SparsePolynomial.scale (13913636889600 : Int) atom0815)))))))) := by decide +kernel
theorem block011_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block011 := by
  rw [block011_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0736_nonneg g hg hA hB) (atom0737_nonneg g hg hA hB)) (add_nonneg (atom0738_nonneg g hg hA hB) (add_nonneg (atom0739_nonneg g hg hA hB) (atom0740_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0741_nonneg g hg hA hB) (atom0742_nonneg g hg hA hB)) (add_nonneg (atom0743_nonneg g hg hA hB) (add_nonneg (atom0744_nonneg g hg hA hB) (atom0745_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0746_nonneg g hg hA hB) (atom0747_nonneg g hg hA hB)) (add_nonneg (atom0748_nonneg g hg hA hB) (add_nonneg (atom0749_nonneg g hg hA hB) (atom0750_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0751_nonneg g hg hA hB) (atom0752_nonneg g hg hA hB)) (add_nonneg (atom0753_nonneg g hg hA hB) (add_nonneg (atom0754_nonneg g hg hA hB) (atom0755_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0756_nonneg g hg hA hB) (atom0757_nonneg g hg hA hB)) (add_nonneg (atom0758_nonneg g hg hA hB) (add_nonneg (atom0759_nonneg g hg hA hB) (atom0760_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0761_nonneg g hg hA hB) (atom0762_nonneg g hg hA hB)) (add_nonneg (atom0763_nonneg g hg hA hB) (add_nonneg (atom0764_nonneg g hg hA hB) (atom0765_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0766_nonneg g hg hA hB) (atom0767_nonneg g hg hA hB)) (add_nonneg (atom0768_nonneg g hg hA hB) (add_nonneg (atom0769_nonneg g hg hA hB) (atom0770_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0771_nonneg g hg hA hB) (atom0772_nonneg g hg hA hB)) (add_nonneg (atom0773_nonneg g hg hA hB) (add_nonneg (atom0774_nonneg g hg hA hB) (atom0775_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0776_nonneg g hg hA hB) (atom0777_nonneg g hg hA hB)) (add_nonneg (atom0778_nonneg g hg hA hB) (add_nonneg (atom0779_nonneg g hg hA hB) (atom0780_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0781_nonneg g hg hA hB) (atom0782_nonneg g hg hA hB)) (add_nonneg (atom0783_nonneg g hg hA hB) (add_nonneg (atom0784_nonneg g hg hA hB) (atom0785_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0786_nonneg g hg hA hB) (atom0787_nonneg g hg hA hB)) (add_nonneg (atom0788_nonneg g hg hA hB) (add_nonneg (atom0789_nonneg g hg hA hB) (atom0790_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0791_nonneg g hg hA hB) (atom0792_nonneg g hg hA hB)) (add_nonneg (atom0793_nonneg g hg hA hB) (add_nonneg (atom0794_nonneg g hg hA hB) (atom0795_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0796_nonneg g hg hA hB) (atom0797_nonneg g hg hA hB)) (add_nonneg (atom0798_nonneg g hg hA hB) (add_nonneg (atom0799_nonneg g hg hA hB) (atom0800_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0801_nonneg g hg hA hB) (atom0802_nonneg g hg hA hB)) (add_nonneg (atom0803_nonneg g hg hA hB) (add_nonneg (atom0804_nonneg g hg hA hB) (atom0805_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0806_nonneg g hg hA hB) (atom0807_nonneg g hg hA hB)) (add_nonneg (atom0808_nonneg g hg hA hB) (add_nonneg (atom0809_nonneg g hg hA hB) (atom0810_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0811_nonneg g hg hA hB) (atom0812_nonneg g hg hA hB)) (add_nonneg (atom0813_nonneg g hg hA hB) (add_nonneg (atom0814_nonneg g hg hA hB) (atom0815_nonneg g hg hA hB))))))))

end APPT.Finite21
