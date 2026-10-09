import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0849 : SparsePolynomial.Poly := [([2,5,13], 1)]
theorem eval_atom0849 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0849 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0849_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (250762389292800 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850 : SparsePolynomial.Poly := [([2,5,14], 1)]
theorem eval_atom0850 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0850 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0850_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (222902250278400 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851 : SparsePolynomial.Poly := [([2,5,15], 1)]
theorem eval_atom0851 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0851 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0851_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225353863526400 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852 : SparsePolynomial.Poly := [([2,5,16], 1)]
theorem eval_atom0852 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0852 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0852_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (215982966528000 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853 : SparsePolynomial.Poly := [([2,5,17], 1)]
theorem eval_atom0853 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0853 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0853_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (216544807987200 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854 : SparsePolynomial.Poly := [([2,5,18], 1)]
theorem eval_atom0854 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0854 = ((g 2) * (g 5) * (g 18)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0854_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (257815027008000 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855 : SparsePolynomial.Poly := [([2,5,19], 1)]
theorem eval_atom0855 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0855 = ((g 2) * (g 5) * (g 19)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0855_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189421289164800 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856 : SparsePolynomial.Poly := [([2,5,20], 1)]
theorem eval_atom0856 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0856 = ((g 2) * (g 5) * (g 20)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0856_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (268578751795200 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857 : SparsePolynomial.Poly := [([2,5,21], 1)]
theorem eval_atom0857 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0857 = ((g 2) * (g 5) * (g 21)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0857_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (215630979379200 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858 : SparsePolynomial.Poly := [([2,5,22], 1)]
theorem eval_atom0858 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0858 = ((g 2) * (g 5) * (g 22)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0858_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (228830374080000 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859 : SparsePolynomial.Poly := [([2,5,23], 1)]
theorem eval_atom0859 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0859 = ((g 2) * (g 5) * (g 23)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0859_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (274763154758400 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0860 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0860 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0860_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126234564825600 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0861 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0861 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0861_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (224731214400000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0862 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0862 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0862_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (202842807552000 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0863 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0863 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0863_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (206600779625328 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0864 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0864 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0864_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (226908137622672 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0865 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0865 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0865_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (237208830575904 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866 : SparsePolynomial.Poly := [([2,6,12], 1)]
theorem eval_atom0866 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0866 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0866_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (263089627314624 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867 : SparsePolynomial.Poly := [([2,6,13], 1)]
theorem eval_atom0867 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0867 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0867_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254449759132800 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868 : SparsePolynomial.Poly := [([2,6,14], 1)]
theorem eval_atom0868 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0868 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0868_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (242135628134400 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869 : SparsePolynomial.Poly := [([2,6,15], 1)]
theorem eval_atom0869 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0869 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0869_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (244608503731200 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870 : SparsePolynomial.Poly := [([2,6,16], 1)]
theorem eval_atom0870 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0870 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0870_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (235258869081600 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871 : SparsePolynomial.Poly := [([2,6,17], 1)]
theorem eval_atom0871 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0871 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0871_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (235841972889600 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872 : SparsePolynomial.Poly := [([2,6,18], 1)]
theorem eval_atom0872 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0872 = ((g 2) * (g 6) * (g 18)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0872_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (274348086566400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873 : SparsePolynomial.Poly := [([2,6,19], 1)]
theorem eval_atom0873 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0873 = ((g 2) * (g 6) * (g 19)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0873_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (220533081753600 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874 : SparsePolynomial.Poly := [([2,6,20], 1)]
theorem eval_atom0874 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0874 = ((g 2) * (g 6) * (g 20)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0874_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (307559875392000 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875 : SparsePolynomial.Poly := [([2,6,21], 1)]
theorem eval_atom0875 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0875 = ((g 2) * (g 6) * (g 21)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0875_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (270329502643200 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876 : SparsePolynomial.Poly := [([2,6,22], 1)]
theorem eval_atom0876 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0876 = ((g 2) * (g 6) * (g 22)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0876_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (299246297011200 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877 : SparsePolynomial.Poly := [([2,6,23], 1)]
theorem eval_atom0877 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0877 = ((g 2) * (g 6) * (g 23)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0877_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (360896477356800 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0878 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0878 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0878_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135493136486400 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0879 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0879 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0879_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254285879232000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0880 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0880 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0880_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (240589825423728 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0881 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0881 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0881_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (257835405193872 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0882 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0882 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0882_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269199215587104 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883 : SparsePolynomial.Poly := [([2,7,12], 1)]
theorem eval_atom0883 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0883 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0883_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (296143129765824 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884 : SparsePolynomial.Poly := [([2,7,13], 1)]
theorem eval_atom0884 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0884 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0884_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (286503931190400 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885 : SparsePolynomial.Poly := [([2,7,14], 1)]
theorem eval_atom0885 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0885 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0885_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (273190469798400 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886 : SparsePolynomial.Poly := [([2,7,15], 1)]
theorem eval_atom0886 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0886 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0886_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (274664015001600 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887 : SparsePolynomial.Poly := [([2,7,16], 1)]
theorem eval_atom0887 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0887 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0887_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264315049958400 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888 : SparsePolynomial.Poly := [([2,7,17], 1)]
theorem eval_atom0888 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0888 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0888_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (263898823372800 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889 : SparsePolynomial.Poly := [([2,7,18], 1)]
theorem eval_atom0889 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0889 = ((g 2) * (g 7) * (g 18)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0889_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (303735015091200 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890 : SparsePolynomial.Poly := [([2,7,19], 1)]
theorem eval_atom0890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0890 = ((g 2) * (g 7) * (g 19)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (253579496755200 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891 : SparsePolynomial.Poly := [([2,7,20], 1)]
theorem eval_atom0891 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0891 = ((g 2) * (g 7) * (g 20)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0891_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (344265776870400 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892 : SparsePolynomial.Poly := [([2,7,21], 1)]
theorem eval_atom0892 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0892 = ((g 2) * (g 7) * (g 21)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0892_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (315353707468800 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893 : SparsePolynomial.Poly := [([2,7,22], 1)]
theorem eval_atom0893 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0893 = ((g 2) * (g 7) * (g 22)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0893_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (352588805184000 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894 : SparsePolynomial.Poly := [([2,7,23], 1)]
theorem eval_atom0894 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0894 = ((g 2) * (g 7) * (g 23)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0894_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (422557288876800 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0895 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0895 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0895_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156809822400000 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0896 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298917689941728 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0897 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0897 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0897_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (285877758467664 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0898 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0898 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0898_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (299464987862304 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0899 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0899 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0899_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (321305938329024 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0900 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0900 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0900_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (309646816617600 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0901 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (294313432089600 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902 : SparsePolynomial.Poly := [([2,8,15], 1)]
theorem eval_atom0902 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0902 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0902_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (293767054156800 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903 : SparsePolynomial.Poly := [([2,8,16], 1)]
theorem eval_atom0903 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0903 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0903_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (281398165977600 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904 : SparsePolynomial.Poly := [([2,8,17], 1)]
theorem eval_atom0904 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0904 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0904_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (278962016256000 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905 : SparsePolynomial.Poly := [([2,8,18], 1)]
theorem eval_atom0905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0905 = ((g 2) * (g 8) * (g 18)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (320232235276800 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906 : SparsePolynomial.Poly := [([2,8,19], 1)]
theorem eval_atom0906 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0906 = ((g 2) * (g 8) * (g 19)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0906_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (274964694681600 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907 : SparsePolynomial.Poly := [([2,8,20], 1)]
theorem eval_atom0907 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0907 = ((g 2) * (g 8) * (g 20)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0907_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (370538952537600 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908 : SparsePolynomial.Poly := [([2,8,21], 1)]
theorem eval_atom0908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0908 = ((g 2) * (g 8) * (g 21)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (353422761753600 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909 : SparsePolynomial.Poly := [([2,8,22], 1)]
theorem eval_atom0909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0909 = ((g 2) * (g 8) * (g 22)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (402453738086400 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910 : SparsePolynomial.Poly := [([2,8,23], 1)]
theorem eval_atom0910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0910 = ((g 2) * (g 8) * (g 23)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (484218100396800 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0911 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (183207987772128 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0912 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (350273600335296 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0913 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0913 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0913_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (338777815302432 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0914 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0914 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0914_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (360661290466752 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0915 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0915 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0915_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (342878612300928 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0916 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0916 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0916_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (324504711894528 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917 : SparsePolynomial.Poly := [([2,9,15], 1)]
theorem eval_atom0917 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0917 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0917_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (320917818083328 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918 : SparsePolynomial.Poly := [([2,9,16], 1)]
theorem eval_atom0918 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0918 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0918_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (305508414025728 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919 : SparsePolynomial.Poly := [([2,9,17], 1)]
theorem eval_atom0919 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0919 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0919_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (300031748425728 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920 : SparsePolynomial.Poly := [([2,9,18], 1)]
theorem eval_atom0920 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0920 = ((g 2) * (g 9) * (g 18)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0920_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (340464919398912 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921 : SparsePolynomial.Poly := [([2,9,19], 1)]
theorem eval_atom0921 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0921 = ((g 2) * (g 9) * (g 19)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0921_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (296563798586880 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922 : SparsePolynomial.Poly := [([2,9,20], 1)]
theorem eval_atom0922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0922 = ((g 2) * (g 9) * (g 20)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (393504476226048 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923 : SparsePolynomial.Poly := [([2,9,21], 1)]
theorem eval_atom0923 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0923 = ((g 2) * (g 9) * (g 21)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0923_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (382161640886784 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924 : SparsePolynomial.Poly := [([2,9,22], 1)]
theorem eval_atom0924 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0924 = ((g 2) * (g 9) * (g 22)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0924_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (436965972664320 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925 : SparsePolynomial.Poly := [([2,9,23], 1)]
theorem eval_atom0925 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0925 = ((g 2) * (g 9) * (g 23)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0925_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (524503690419456 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0926 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0926 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0926_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (208165732793568 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0927 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0927 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0927_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (407982508176672 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0928 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0928 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0928_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (422721834144192 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block013 : SparsePolynomial.Poly := [([2,5,13], 250762389292800), ([2,5,14], 222902250278400), ([2,5,15], 225353863526400), ([2,5,16], 215982966528000), ([2,5,17], 216544807987200), ([2,5,18], 257815027008000), ([2,5,19], 189421289164800), ([2,5,20], 268578751795200), ([2,5,21], 215630979379200), ([2,5,22], 228830374080000), ([2,5,23], 274763154758400), ([2,6,6], 126234564825600), ([2,6,7], 224731214400000), ([2,6,8], 202842807552000), ([2,6,9], 206600779625328), ([2,6,10], 226908137622672), ([2,6,11], 237208830575904), ([2,6,12], 263089627314624), ([2,6,13], 254449759132800), ([2,6,14], 242135628134400), ([2,6,15], 244608503731200), ([2,6,16], 235258869081600), ([2,6,17], 235841972889600), ([2,6,18], 274348086566400), ([2,6,19], 220533081753600), ([2,6,20], 307559875392000), ([2,6,21], 270329502643200), ([2,6,22], 299246297011200), ([2,6,23], 360896477356800), ([2,7,7], 135493136486400), ([2,7,8], 254285879232000), ([2,7,9], 240589825423728), ([2,7,10], 257835405193872), ([2,7,11], 269199215587104), ([2,7,12], 296143129765824), ([2,7,13], 286503931190400), ([2,7,14], 273190469798400), ([2,7,15], 274664015001600), ([2,7,16], 264315049958400), ([2,7,17], 263898823372800), ([2,7,18], 303735015091200), ([2,7,19], 253579496755200), ([2,7,20], 344265776870400), ([2,7,21], 315353707468800), ([2,7,22], 352588805184000), ([2,7,23], 422557288876800), ([2,8,8], 156809822400000), ([2,8,9], 298917689941728), ([2,8,10], 285877758467664), ([2,8,11], 299464987862304), ([2,8,12], 321305938329024), ([2,8,13], 309646816617600), ([2,8,14], 294313432089600), ([2,8,15], 293767054156800), ([2,8,16], 281398165977600), ([2,8,17], 278962016256000), ([2,8,18], 320232235276800), ([2,8,19], 274964694681600), ([2,8,20], 370538952537600), ([2,8,21], 353422761753600), ([2,8,22], 402453738086400), ([2,8,23], 484218100396800), ([2,9,9], 183207987772128), ([2,9,10], 350273600335296), ([2,9,11], 338777815302432), ([2,9,12], 360661290466752), ([2,9,13], 342878612300928), ([2,9,14], 324504711894528), ([2,9,15], 320917818083328), ([2,9,16], 305508414025728), ([2,9,17], 300031748425728), ([2,9,18], 340464919398912), ([2,9,19], 296563798586880), ([2,9,20], 393504476226048), ([2,9,21], 382161640886784), ([2,9,22], 436965972664320), ([2,9,23], 524503690419456), ([2,10,10], 208165732793568), ([2,10,11], 407982508176672), ([2,10,12], 422721834144192)]
theorem block013_data : block013 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (250762389292800 : Int) atom0849) (SparsePolynomial.scale (222902250278400 : Int) atom0850)) (SparsePolynomial.merge (SparsePolynomial.scale (225353863526400 : Int) atom0851) (SparsePolynomial.merge (SparsePolynomial.scale (215982966528000 : Int) atom0852) (SparsePolynomial.scale (216544807987200 : Int) atom0853)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (257815027008000 : Int) atom0854) (SparsePolynomial.scale (189421289164800 : Int) atom0855)) (SparsePolynomial.merge (SparsePolynomial.scale (268578751795200 : Int) atom0856) (SparsePolynomial.merge (SparsePolynomial.scale (215630979379200 : Int) atom0857) (SparsePolynomial.scale (228830374080000 : Int) atom0858))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (274763154758400 : Int) atom0859) (SparsePolynomial.scale (126234564825600 : Int) atom0860)) (SparsePolynomial.merge (SparsePolynomial.scale (224731214400000 : Int) atom0861) (SparsePolynomial.merge (SparsePolynomial.scale (202842807552000 : Int) atom0862) (SparsePolynomial.scale (206600779625328 : Int) atom0863)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (226908137622672 : Int) atom0864) (SparsePolynomial.scale (237208830575904 : Int) atom0865)) (SparsePolynomial.merge (SparsePolynomial.scale (263089627314624 : Int) atom0866) (SparsePolynomial.merge (SparsePolynomial.scale (254449759132800 : Int) atom0867) (SparsePolynomial.scale (242135628134400 : Int) atom0868)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (244608503731200 : Int) atom0869) (SparsePolynomial.scale (235258869081600 : Int) atom0870)) (SparsePolynomial.merge (SparsePolynomial.scale (235841972889600 : Int) atom0871) (SparsePolynomial.merge (SparsePolynomial.scale (274348086566400 : Int) atom0872) (SparsePolynomial.scale (220533081753600 : Int) atom0873)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (307559875392000 : Int) atom0874) (SparsePolynomial.scale (270329502643200 : Int) atom0875)) (SparsePolynomial.merge (SparsePolynomial.scale (299246297011200 : Int) atom0876) (SparsePolynomial.merge (SparsePolynomial.scale (360896477356800 : Int) atom0877) (SparsePolynomial.scale (135493136486400 : Int) atom0878))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (254285879232000 : Int) atom0879) (SparsePolynomial.scale (240589825423728 : Int) atom0880)) (SparsePolynomial.merge (SparsePolynomial.scale (257835405193872 : Int) atom0881) (SparsePolynomial.merge (SparsePolynomial.scale (269199215587104 : Int) atom0882) (SparsePolynomial.scale (296143129765824 : Int) atom0883)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (286503931190400 : Int) atom0884) (SparsePolynomial.scale (273190469798400 : Int) atom0885)) (SparsePolynomial.merge (SparsePolynomial.scale (274664015001600 : Int) atom0886) (SparsePolynomial.merge (SparsePolynomial.scale (264315049958400 : Int) atom0887) (SparsePolynomial.scale (263898823372800 : Int) atom0888))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (303735015091200 : Int) atom0889) (SparsePolynomial.scale (253579496755200 : Int) atom0890)) (SparsePolynomial.merge (SparsePolynomial.scale (344265776870400 : Int) atom0891) (SparsePolynomial.merge (SparsePolynomial.scale (315353707468800 : Int) atom0892) (SparsePolynomial.scale (352588805184000 : Int) atom0893)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (422557288876800 : Int) atom0894) (SparsePolynomial.scale (156809822400000 : Int) atom0895)) (SparsePolynomial.merge (SparsePolynomial.scale (298917689941728 : Int) atom0896) (SparsePolynomial.merge (SparsePolynomial.scale (285877758467664 : Int) atom0897) (SparsePolynomial.scale (299464987862304 : Int) atom0898))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (321305938329024 : Int) atom0899) (SparsePolynomial.scale (309646816617600 : Int) atom0900)) (SparsePolynomial.merge (SparsePolynomial.scale (294313432089600 : Int) atom0901) (SparsePolynomial.merge (SparsePolynomial.scale (293767054156800 : Int) atom0902) (SparsePolynomial.scale (281398165977600 : Int) atom0903)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (278962016256000 : Int) atom0904) (SparsePolynomial.scale (320232235276800 : Int) atom0905)) (SparsePolynomial.merge (SparsePolynomial.scale (274964694681600 : Int) atom0906) (SparsePolynomial.merge (SparsePolynomial.scale (370538952537600 : Int) atom0907) (SparsePolynomial.scale (353422761753600 : Int) atom0908)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (402453738086400 : Int) atom0909) (SparsePolynomial.scale (484218100396800 : Int) atom0910)) (SparsePolynomial.merge (SparsePolynomial.scale (183207987772128 : Int) atom0911) (SparsePolynomial.merge (SparsePolynomial.scale (350273600335296 : Int) atom0912) (SparsePolynomial.scale (338777815302432 : Int) atom0913)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (360661290466752 : Int) atom0914) (SparsePolynomial.scale (342878612300928 : Int) atom0915)) (SparsePolynomial.merge (SparsePolynomial.scale (324504711894528 : Int) atom0916) (SparsePolynomial.merge (SparsePolynomial.scale (320917818083328 : Int) atom0917) (SparsePolynomial.scale (305508414025728 : Int) atom0918))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (300031748425728 : Int) atom0919) (SparsePolynomial.scale (340464919398912 : Int) atom0920)) (SparsePolynomial.merge (SparsePolynomial.scale (296563798586880 : Int) atom0921) (SparsePolynomial.merge (SparsePolynomial.scale (393504476226048 : Int) atom0922) (SparsePolynomial.scale (382161640886784 : Int) atom0923)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (436965972664320 : Int) atom0924) (SparsePolynomial.scale (524503690419456 : Int) atom0925)) (SparsePolynomial.merge (SparsePolynomial.scale (208165732793568 : Int) atom0926) (SparsePolynomial.merge (SparsePolynomial.scale (407982508176672 : Int) atom0927) (SparsePolynomial.scale (422721834144192 : Int) atom0928)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block013 := by
  rw [block013_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0849_nonneg g hg hA hB) (atom0850_nonneg g hg hA hB)) (add_nonneg (atom0851_nonneg g hg hA hB) (add_nonneg (atom0852_nonneg g hg hA hB) (atom0853_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0854_nonneg g hg hA hB) (atom0855_nonneg g hg hA hB)) (add_nonneg (atom0856_nonneg g hg hA hB) (add_nonneg (atom0857_nonneg g hg hA hB) (atom0858_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0859_nonneg g hg hA hB) (atom0860_nonneg g hg hA hB)) (add_nonneg (atom0861_nonneg g hg hA hB) (add_nonneg (atom0862_nonneg g hg hA hB) (atom0863_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0864_nonneg g hg hA hB) (atom0865_nonneg g hg hA hB)) (add_nonneg (atom0866_nonneg g hg hA hB) (add_nonneg (atom0867_nonneg g hg hA hB) (atom0868_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0869_nonneg g hg hA hB) (atom0870_nonneg g hg hA hB)) (add_nonneg (atom0871_nonneg g hg hA hB) (add_nonneg (atom0872_nonneg g hg hA hB) (atom0873_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0874_nonneg g hg hA hB) (atom0875_nonneg g hg hA hB)) (add_nonneg (atom0876_nonneg g hg hA hB) (add_nonneg (atom0877_nonneg g hg hA hB) (atom0878_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0879_nonneg g hg hA hB) (atom0880_nonneg g hg hA hB)) (add_nonneg (atom0881_nonneg g hg hA hB) (add_nonneg (atom0882_nonneg g hg hA hB) (atom0883_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0884_nonneg g hg hA hB) (atom0885_nonneg g hg hA hB)) (add_nonneg (atom0886_nonneg g hg hA hB) (add_nonneg (atom0887_nonneg g hg hA hB) (atom0888_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0889_nonneg g hg hA hB) (atom0890_nonneg g hg hA hB)) (add_nonneg (atom0891_nonneg g hg hA hB) (add_nonneg (atom0892_nonneg g hg hA hB) (atom0893_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0894_nonneg g hg hA hB) (atom0895_nonneg g hg hA hB)) (add_nonneg (atom0896_nonneg g hg hA hB) (add_nonneg (atom0897_nonneg g hg hA hB) (atom0898_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0899_nonneg g hg hA hB) (atom0900_nonneg g hg hA hB)) (add_nonneg (atom0901_nonneg g hg hA hB) (add_nonneg (atom0902_nonneg g hg hA hB) (atom0903_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0904_nonneg g hg hA hB) (atom0905_nonneg g hg hA hB)) (add_nonneg (atom0906_nonneg g hg hA hB) (add_nonneg (atom0907_nonneg g hg hA hB) (atom0908_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0909_nonneg g hg hA hB) (atom0910_nonneg g hg hA hB)) (add_nonneg (atom0911_nonneg g hg hA hB) (add_nonneg (atom0912_nonneg g hg hA hB) (atom0913_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0914_nonneg g hg hA hB) (atom0915_nonneg g hg hA hB)) (add_nonneg (atom0916_nonneg g hg hA hB) (add_nonneg (atom0917_nonneg g hg hA hB) (atom0918_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0919_nonneg g hg hA hB) (atom0920_nonneg g hg hA hB)) (add_nonneg (atom0921_nonneg g hg hA hB) (add_nonneg (atom0922_nonneg g hg hA hB) (atom0923_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0924_nonneg g hg hA hB) (atom0925_nonneg g hg hA hB)) (add_nonneg (atom0926_nonneg g hg hA hB) (add_nonneg (atom0927_nonneg g hg hA hB) (atom0928_nonneg g hg hA hB))))))))

end APPT.Finite24
