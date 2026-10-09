import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0735 : SparsePolynomial.Poly := [([4,11,17], 1)]
theorem eval_atom0735 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0735 = ((g 4) * (g 11) * (g 17)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0735_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13537883520 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736 : SparsePolynomial.Poly := [([4,12,12], 1)]
theorem eval_atom0736 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4983552000 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737 : SparsePolynomial.Poly := [([4,12,13], 1)]
theorem eval_atom0737 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8680213920 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738 : SparsePolynomial.Poly := [([4,12,14], 1)]
theorem eval_atom0738 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13712925600 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739 : SparsePolynomial.Poly := [([4,12,15], 1)]
theorem eval_atom0739 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 4) * (g 12) * (g 15)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13122490080 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740 : SparsePolynomial.Poly := [([4,12,16], 1)]
theorem eval_atom0740 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 4) * (g 12) * (g 16)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9202835040 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741 : SparsePolynomial.Poly := [([4,12,17], 1)]
theorem eval_atom0741 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 4) * (g 12) * (g 17)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14166482400 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742 : SparsePolynomial.Poly := [([4,13,13], 1)]
theorem eval_atom0742 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3690344448 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743 : SparsePolynomial.Poly := [([4,13,14], 1)]
theorem eval_atom0743 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11120967960 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744 : SparsePolynomial.Poly := [([4,13,15], 1)]
theorem eval_atom0744 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 4) * (g 13) * (g 15)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11594877840 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745 : SparsePolynomial.Poly := [([4,13,16], 1)]
theorem eval_atom0745 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 4) * (g 13) * (g 16)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8682470720 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746 : SparsePolynomial.Poly := [([4,13,17], 1)]
theorem eval_atom0746 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 4) * (g 13) * (g 17)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10514692440 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747 : SparsePolynomial.Poly := [([4,14,14], 1)]
theorem eval_atom0747 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7996131000 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748 : SparsePolynomial.Poly := [([4,14,15], 1)]
theorem eval_atom0748 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 4) * (g 14) * (g 15)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12540252120 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749 : SparsePolynomial.Poly := [([4,14,16], 1)]
theorem eval_atom0749 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 4) * (g 14) * (g 16)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8869733360 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750 : SparsePolynomial.Poly := [([4,14,17], 1)]
theorem eval_atom0750 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 4) * (g 14) * (g 17)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11595222000 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751 : SparsePolynomial.Poly := [([4,15,15], 1)]
theorem eval_atom0751 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3641223600 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752 : SparsePolynomial.Poly := [([4,15,16], 1)]
theorem eval_atom0752 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4763779440 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753 : SparsePolynomial.Poly := [([4,15,17], 1)]
theorem eval_atom0753 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7669965240 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754 : SparsePolynomial.Poly := [([4,16,17], 1)]
theorem eval_atom0754 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2648638440 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755 : SparsePolynomial.Poly := [([4,17,17], 1)]
theorem eval_atom0755 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2764487880 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom0756 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (580913280 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom0757 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (807960960 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom0758 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom0759 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78704640 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760 : SparsePolynomial.Poly := [([5,5,12], 1)]
theorem eval_atom0760 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (960689520 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom0761 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762 : SparsePolynomial.Poly := [([5,6,10], 1)]
theorem eval_atom0762 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 5) * (g 6) * (g 10)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763 : SparsePolynomial.Poly := [([5,6,11], 1)]
theorem eval_atom0763 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 5) * (g 6) * (g 11)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764 : SparsePolynomial.Poly := [([5,6,12], 1)]
theorem eval_atom0764 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 5) * (g 6) * (g 12)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1275597792 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765 : SparsePolynomial.Poly := [([5,6,14], 1)]
theorem eval_atom0765 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173304000 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766 : SparsePolynomial.Poly := [([5,6,15], 1)]
theorem eval_atom0766 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767 : SparsePolynomial.Poly := [([5,6,16], 1)]
theorem eval_atom0767 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 5) * (g 6) * (g 16)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768 : SparsePolynomial.Poly := [([5,6,17], 1)]
theorem eval_atom0768 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom0769 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126817920 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770 : SparsePolynomial.Poly := [([5,7,10], 1)]
theorem eval_atom0770 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0770 = ((g 5) * (g 7) * (g 10)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0770_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157409280 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771 : SparsePolynomial.Poly := [([5,7,11], 1)]
theorem eval_atom0771 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0771 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0771_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (314818560 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772 : SparsePolynomial.Poly := [([5,7,12], 1)]
theorem eval_atom0772 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0772 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0772_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1398790080 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773 : SparsePolynomial.Poly := [([5,7,13], 1)]
theorem eval_atom0773 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0773 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0773_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (748771920 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774 : SparsePolynomial.Poly := [([5,7,14], 1)]
theorem eval_atom0774 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0774 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0774_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1544502240 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775 : SparsePolynomial.Poly := [([5,7,15], 1)]
theorem eval_atom0775 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0775 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0775_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3018304080 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776 : SparsePolynomial.Poly := [([5,7,16], 1)]
theorem eval_atom0776 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0776 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0776_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4822144560 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777 : SparsePolynomial.Poly := [([5,7,17], 1)]
theorem eval_atom0777 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0777 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0777_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6797629440 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom0778 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779 : SparsePolynomial.Poly := [([5,8,9], 1)]
theorem eval_atom0779 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0779 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0779_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (832953600 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780 : SparsePolynomial.Poly := [([5,8,10], 1)]
theorem eval_atom0780 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0780 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0780_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (993588480 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781 : SparsePolynomial.Poly := [([5,8,11], 1)]
theorem eval_atom0781 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0781 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0781_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1154223360 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782 : SparsePolynomial.Poly := [([5,8,12], 1)]
theorem eval_atom0782 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0782 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0782_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2225592000 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783 : SparsePolynomial.Poly := [([5,8,13], 1)]
theorem eval_atom0783 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0783 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0783_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1908204720 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784 : SparsePolynomial.Poly := [([5,8,14], 1)]
theorem eval_atom0784 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0784 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0784_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3183133920 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785 : SparsePolynomial.Poly := [([5,8,15], 1)]
theorem eval_atom0785 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0785 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0785_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4551344880 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786 : SparsePolynomial.Poly := [([5,8,16], 1)]
theorem eval_atom0786 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0786 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0786_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6551182800 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787 : SparsePolynomial.Poly := [([5,8,17], 1)]
theorem eval_atom0787 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0787 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0787_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8696665440 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788 : SparsePolynomial.Poly := [([5,9,9], 1)]
theorem eval_atom0788 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1063635840 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789 : SparsePolynomial.Poly := [([5,9,10], 1)]
theorem eval_atom0789 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0789 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0789_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1890097920 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790 : SparsePolynomial.Poly := [([5,9,11], 1)]
theorem eval_atom0790 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0790 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0790_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2003639040 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791 : SparsePolynomial.Poly := [([5,9,12], 1)]
theorem eval_atom0791 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0791 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0791_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3152367360 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792 : SparsePolynomial.Poly := [([5,9,13], 1)]
theorem eval_atom0792 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0792 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0792_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2936154480 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793 : SparsePolynomial.Poly := [([5,9,14], 1)]
theorem eval_atom0793 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0793 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0793_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4697875680 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794 : SparsePolynomial.Poly := [([5,9,15], 1)]
theorem eval_atom0794 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0794 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0794_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5778953520 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795 : SparsePolynomial.Poly := [([5,9,16], 1)]
theorem eval_atom0795 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0795 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0795_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7877275920 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796 : SparsePolynomial.Poly := [([5,9,17], 1)]
theorem eval_atom0796 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0796 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0796_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10096083360 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797 : SparsePolynomial.Poly := [([5,10,10], 1)]
theorem eval_atom0797 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1707696000 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798 : SparsePolynomial.Poly := [([5,10,11], 1)]
theorem eval_atom0798 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0798 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0798_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3097532160 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799 : SparsePolynomial.Poly := [([5,10,12], 1)]
theorem eval_atom0799 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0799 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0799_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4211694720 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800 : SparsePolynomial.Poly := [([5,10,13], 1)]
theorem eval_atom0800 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0800 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0800_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3949897200 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801 : SparsePolynomial.Poly := [([5,10,14], 1)]
theorem eval_atom0801 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0801 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0801_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6236164320 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802 : SparsePolynomial.Poly := [([5,10,15], 1)]
theorem eval_atom0802 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0802 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0802_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6642556080 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803 : SparsePolynomial.Poly := [([5,10,16], 1)]
theorem eval_atom0803 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0803 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0803_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8636322960 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804 : SparsePolynomial.Poly := [([5,10,17], 1)]
theorem eval_atom0804 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0804 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0804_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11022864480 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805 : SparsePolynomial.Poly := [([5,11,11], 1)]
theorem eval_atom0805 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2604689280 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806 : SparsePolynomial.Poly := [([5,11,12], 1)]
theorem eval_atom0806 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0806 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0806_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5147904960 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807 : SparsePolynomial.Poly := [([5,11,13], 1)]
theorem eval_atom0807 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0807 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0807_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4759343280 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808 : SparsePolynomial.Poly := [([5,11,14], 1)]
theorem eval_atom0808 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0808 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0808_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7588308960 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809 : SparsePolynomial.Poly := [([5,11,15], 1)]
theorem eval_atom0809 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0809 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0809_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8197968240 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810 : SparsePolynomial.Poly := [([5,11,16], 1)]
theorem eval_atom0810 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0810 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0810_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8997500880 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811 : SparsePolynomial.Poly := [([5,11,17], 1)]
theorem eval_atom0811 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0811 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0811_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13443213600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812 : SparsePolynomial.Poly := [([5,12,12], 1)]
theorem eval_atom0812 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4203601920 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813 : SparsePolynomial.Poly := [([5,12,13], 1)]
theorem eval_atom0813 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0813 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0813_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7777390680 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814 : SparsePolynomial.Poly := [([5,12,14], 1)]
theorem eval_atom0814 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0814 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0814_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12945232800 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block010 : SparsePolynomial.Poly := [([4,11,17], 13537883520), ([4,12,12], 4983552000), ([4,12,13], 8680213920), ([4,12,14], 13712925600), ([4,12,15], 13122490080), ([4,12,16], 9202835040), ([4,12,17], 14166482400), ([4,13,13], 3690344448), ([4,13,14], 11120967960), ([4,13,15], 11594877840), ([4,13,16], 8682470720), ([4,13,17], 10514692440), ([4,14,14], 7996131000), ([4,14,15], 12540252120), ([4,14,16], 8869733360), ([4,14,17], 11595222000), ([4,15,15], 3641223600), ([4,15,16], 4763779440), ([4,15,17], 7669965240), ([4,16,17], 2648638440), ([4,17,17], 2764487880), ([5,5,5], 580913280), ([5,5,6], 807960960), ([5,5,7], 103864320), ([5,5,8], 78704640), ([5,5,12], 960689520), ([5,6,6], 546687360), ([5,6,10], 103864320), ([5,6,11], 207728640), ([5,6,12], 1275597792), ([5,6,14], 173304000), ([5,6,15], 1180247040), ([5,6,16], 2293143552), ([5,6,17], 3586383360), ([5,7,7], 126817920), ([5,7,10], 157409280), ([5,7,11], 314818560), ([5,7,12], 1398790080), ([5,7,13], 748771920), ([5,7,14], 1544502240), ([5,7,15], 3018304080), ([5,7,16], 4822144560), ([5,7,17], 6797629440), ([5,8,8], 546687360), ([5,8,9], 832953600), ([5,8,10], 993588480), ([5,8,11], 1154223360), ([5,8,12], 2225592000), ([5,8,13], 1908204720), ([5,8,14], 3183133920), ([5,8,15], 4551344880), ([5,8,16], 6551182800), ([5,8,17], 8696665440), ([5,9,9], 1063635840), ([5,9,10], 1890097920), ([5,9,11], 2003639040), ([5,9,12], 3152367360), ([5,9,13], 2936154480), ([5,9,14], 4697875680), ([5,9,15], 5778953520), ([5,9,16], 7877275920), ([5,9,17], 10096083360), ([5,10,10], 1707696000), ([5,10,11], 3097532160), ([5,10,12], 4211694720), ([5,10,13], 3949897200), ([5,10,14], 6236164320), ([5,10,15], 6642556080), ([5,10,16], 8636322960), ([5,10,17], 11022864480), ([5,11,11], 2604689280), ([5,11,12], 5147904960), ([5,11,13], 4759343280), ([5,11,14], 7588308960), ([5,11,15], 8197968240), ([5,11,16], 8997500880), ([5,11,17], 13443213600), ([5,12,12], 4203601920), ([5,12,13], 7777390680), ([5,12,14], 12945232800)]
theorem block010_data : block010 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13537883520 : Int) atom0735) (SparsePolynomial.scale (4983552000 : Int) atom0736)) (SparsePolynomial.merge (SparsePolynomial.scale (8680213920 : Int) atom0737) (SparsePolynomial.merge (SparsePolynomial.scale (13712925600 : Int) atom0738) (SparsePolynomial.scale (13122490080 : Int) atom0739)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9202835040 : Int) atom0740) (SparsePolynomial.scale (14166482400 : Int) atom0741)) (SparsePolynomial.merge (SparsePolynomial.scale (3690344448 : Int) atom0742) (SparsePolynomial.merge (SparsePolynomial.scale (11120967960 : Int) atom0743) (SparsePolynomial.scale (11594877840 : Int) atom0744))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8682470720 : Int) atom0745) (SparsePolynomial.scale (10514692440 : Int) atom0746)) (SparsePolynomial.merge (SparsePolynomial.scale (7996131000 : Int) atom0747) (SparsePolynomial.merge (SparsePolynomial.scale (12540252120 : Int) atom0748) (SparsePolynomial.scale (8869733360 : Int) atom0749)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11595222000 : Int) atom0750) (SparsePolynomial.scale (3641223600 : Int) atom0751)) (SparsePolynomial.merge (SparsePolynomial.scale (4763779440 : Int) atom0752) (SparsePolynomial.merge (SparsePolynomial.scale (7669965240 : Int) atom0753) (SparsePolynomial.scale (2648638440 : Int) atom0754)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2764487880 : Int) atom0755) (SparsePolynomial.scale (580913280 : Int) atom0756)) (SparsePolynomial.merge (SparsePolynomial.scale (807960960 : Int) atom0757) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0758) (SparsePolynomial.scale (78704640 : Int) atom0759)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (960689520 : Int) atom0760) (SparsePolynomial.scale (546687360 : Int) atom0761)) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0762) (SparsePolynomial.merge (SparsePolynomial.scale (207728640 : Int) atom0763) (SparsePolynomial.scale (1275597792 : Int) atom0764))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (173304000 : Int) atom0765) (SparsePolynomial.scale (1180247040 : Int) atom0766)) (SparsePolynomial.merge (SparsePolynomial.scale (2293143552 : Int) atom0767) (SparsePolynomial.merge (SparsePolynomial.scale (3586383360 : Int) atom0768) (SparsePolynomial.scale (126817920 : Int) atom0769)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (157409280 : Int) atom0770) (SparsePolynomial.scale (314818560 : Int) atom0771)) (SparsePolynomial.merge (SparsePolynomial.scale (1398790080 : Int) atom0772) (SparsePolynomial.merge (SparsePolynomial.scale (748771920 : Int) atom0773) (SparsePolynomial.scale (1544502240 : Int) atom0774))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3018304080 : Int) atom0775) (SparsePolynomial.scale (4822144560 : Int) atom0776)) (SparsePolynomial.merge (SparsePolynomial.scale (6797629440 : Int) atom0777) (SparsePolynomial.merge (SparsePolynomial.scale (546687360 : Int) atom0778) (SparsePolynomial.scale (832953600 : Int) atom0779)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (993588480 : Int) atom0780) (SparsePolynomial.scale (1154223360 : Int) atom0781)) (SparsePolynomial.merge (SparsePolynomial.scale (2225592000 : Int) atom0782) (SparsePolynomial.merge (SparsePolynomial.scale (1908204720 : Int) atom0783) (SparsePolynomial.scale (3183133920 : Int) atom0784))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4551344880 : Int) atom0785) (SparsePolynomial.scale (6551182800 : Int) atom0786)) (SparsePolynomial.merge (SparsePolynomial.scale (8696665440 : Int) atom0787) (SparsePolynomial.merge (SparsePolynomial.scale (1063635840 : Int) atom0788) (SparsePolynomial.scale (1890097920 : Int) atom0789)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2003639040 : Int) atom0790) (SparsePolynomial.scale (3152367360 : Int) atom0791)) (SparsePolynomial.merge (SparsePolynomial.scale (2936154480 : Int) atom0792) (SparsePolynomial.merge (SparsePolynomial.scale (4697875680 : Int) atom0793) (SparsePolynomial.scale (5778953520 : Int) atom0794)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7877275920 : Int) atom0795) (SparsePolynomial.scale (10096083360 : Int) atom0796)) (SparsePolynomial.merge (SparsePolynomial.scale (1707696000 : Int) atom0797) (SparsePolynomial.merge (SparsePolynomial.scale (3097532160 : Int) atom0798) (SparsePolynomial.scale (4211694720 : Int) atom0799)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3949897200 : Int) atom0800) (SparsePolynomial.scale (6236164320 : Int) atom0801)) (SparsePolynomial.merge (SparsePolynomial.scale (6642556080 : Int) atom0802) (SparsePolynomial.merge (SparsePolynomial.scale (8636322960 : Int) atom0803) (SparsePolynomial.scale (11022864480 : Int) atom0804))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2604689280 : Int) atom0805) (SparsePolynomial.scale (5147904960 : Int) atom0806)) (SparsePolynomial.merge (SparsePolynomial.scale (4759343280 : Int) atom0807) (SparsePolynomial.merge (SparsePolynomial.scale (7588308960 : Int) atom0808) (SparsePolynomial.scale (8197968240 : Int) atom0809)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8997500880 : Int) atom0810) (SparsePolynomial.scale (13443213600 : Int) atom0811)) (SparsePolynomial.merge (SparsePolynomial.scale (4203601920 : Int) atom0812) (SparsePolynomial.merge (SparsePolynomial.scale (7777390680 : Int) atom0813) (SparsePolynomial.scale (12945232800 : Int) atom0814)))))))) := by decide +kernel
theorem block010_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block010 := by
  rw [block010_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0735_nonneg g hg hA hB) (atom0736_nonneg g hg hA hB)) (add_nonneg (atom0737_nonneg g hg hA hB) (add_nonneg (atom0738_nonneg g hg hA hB) (atom0739_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0740_nonneg g hg hA hB) (atom0741_nonneg g hg hA hB)) (add_nonneg (atom0742_nonneg g hg hA hB) (add_nonneg (atom0743_nonneg g hg hA hB) (atom0744_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0745_nonneg g hg hA hB) (atom0746_nonneg g hg hA hB)) (add_nonneg (atom0747_nonneg g hg hA hB) (add_nonneg (atom0748_nonneg g hg hA hB) (atom0749_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0750_nonneg g hg hA hB) (atom0751_nonneg g hg hA hB)) (add_nonneg (atom0752_nonneg g hg hA hB) (add_nonneg (atom0753_nonneg g hg hA hB) (atom0754_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0755_nonneg g hg hA hB) (atom0756_nonneg g hg hA hB)) (add_nonneg (atom0757_nonneg g hg hA hB) (add_nonneg (atom0758_nonneg g hg hA hB) (atom0759_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0760_nonneg g hg hA hB) (atom0761_nonneg g hg hA hB)) (add_nonneg (atom0762_nonneg g hg hA hB) (add_nonneg (atom0763_nonneg g hg hA hB) (atom0764_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0765_nonneg g hg hA hB) (atom0766_nonneg g hg hA hB)) (add_nonneg (atom0767_nonneg g hg hA hB) (add_nonneg (atom0768_nonneg g hg hA hB) (atom0769_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0770_nonneg g hg hA hB) (atom0771_nonneg g hg hA hB)) (add_nonneg (atom0772_nonneg g hg hA hB) (add_nonneg (atom0773_nonneg g hg hA hB) (atom0774_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0775_nonneg g hg hA hB) (atom0776_nonneg g hg hA hB)) (add_nonneg (atom0777_nonneg g hg hA hB) (add_nonneg (atom0778_nonneg g hg hA hB) (atom0779_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0780_nonneg g hg hA hB) (atom0781_nonneg g hg hA hB)) (add_nonneg (atom0782_nonneg g hg hA hB) (add_nonneg (atom0783_nonneg g hg hA hB) (atom0784_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0785_nonneg g hg hA hB) (atom0786_nonneg g hg hA hB)) (add_nonneg (atom0787_nonneg g hg hA hB) (add_nonneg (atom0788_nonneg g hg hA hB) (atom0789_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0790_nonneg g hg hA hB) (atom0791_nonneg g hg hA hB)) (add_nonneg (atom0792_nonneg g hg hA hB) (add_nonneg (atom0793_nonneg g hg hA hB) (atom0794_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0795_nonneg g hg hA hB) (atom0796_nonneg g hg hA hB)) (add_nonneg (atom0797_nonneg g hg hA hB) (add_nonneg (atom0798_nonneg g hg hA hB) (atom0799_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0800_nonneg g hg hA hB) (atom0801_nonneg g hg hA hB)) (add_nonneg (atom0802_nonneg g hg hA hB) (add_nonneg (atom0803_nonneg g hg hA hB) (atom0804_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0805_nonneg g hg hA hB) (atom0806_nonneg g hg hA hB)) (add_nonneg (atom0807_nonneg g hg hA hB) (add_nonneg (atom0808_nonneg g hg hA hB) (atom0809_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0810_nonneg g hg hA hB) (atom0811_nonneg g hg hA hB)) (add_nonneg (atom0812_nonneg g hg hA hB) (add_nonneg (atom0813_nonneg g hg hA hB) (atom0814_nonneg g hg hA hB))))))))

end APPT.Finite18
