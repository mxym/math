import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Scalar tools for the actual truncation construction. The rational expression
below is not identified with `entryDefect` in this module. That geometric
identity must be proved separately before using these results for sharpness.
-/

noncomputable section

open Filter Topology

namespace Entry005

/-- The scalar expression in equation (D) of the truncation calculation. -/
def truncationRationalDefect (d : ℕ) (t : ℝ) : ℝ :=
  t ^ (d - 1) *
      ((d : ℝ) * (d - 1) - (d + 1) * (d - 2) * t - 2 * t ^ d) /
    ((d + 1) * (1 - t ^ d) * (d + 1 + (d - 1) * t ^ (d - 1)))

/-- The continuous coefficient remaining after dividing equation (D) by
`t^(d-1)`. -/
def truncationRationalCoefficient (d : ℕ) (t : ℝ) : ℝ :=
  ((d : ℝ) * (d - 1) - (d + 1) * (d - 2) * t - 2 * t ^ d) /
    ((d + 1) * (1 - t ^ d) * (d + 1 + (d - 1) * t ^ (d - 1)))

theorem truncation_rational_defect_factor (d : ℕ) (t : ℝ) :
    truncationRationalDefect d t = t ^ (d - 1) * truncationRationalCoefficient d t := by
  simp only [truncationRationalDefect, truncationRationalCoefficient, mul_div_assoc]

theorem truncation_rational_coefficient_pos {d : ℕ} (hd : 3 ≤ d)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < truncationRationalCoefficient d t := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hd2 : 0 < (d : ℝ) - 2 := by linarith
  have hdt : 0 < (d : ℝ) + 1 := by positivity
  have hd0 : d ≠ 0 := by omega
  have hp : t ^ d < 1 := pow_lt_one₀ ht.le ht1 hd0
  have hpg : 0 < 1 - t ^ d := sub_pos.mpr hp
  have htg : 0 < 1 - t := sub_pos.mpr ht1
  have hbracket :
      (d : ℝ) * (d - 1) - (d + 1) * (d - 2) * t - 2 * t ^ d =
        (d + 1) * (d - 2) * (1 - t) + 2 * (1 - t ^ d) := by ring
  unfold truncationRationalCoefficient
  rw [hbracket]
  apply div_pos
  · positivity
  · have hbase : 0 < (d : ℝ) + 1 + (d - 1) * t ^ (d - 1) := by positivity
    positivity

theorem truncation_rational_defect_pos {d : ℕ} (hd : 3 ≤ d)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < truncationRationalDefect d t := by
  rw [truncation_rational_defect_factor]
  exact mul_pos (pow_pos ht _) (truncation_rational_coefficient_pos hd ht ht1)

theorem truncation_rational_coefficient_tendsto {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (truncationRationalCoefficient d) (𝓝 0)
      (𝓝 ((d : ℝ) * (d - 1) / (d + 1) ^ 2)) := by
  have hn : d - 1 ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have hden :
      (d : ℝ) + 1 ≠ 0 := by positivity
  have hc : ContinuousAt (truncationRationalCoefficient d) 0 := by
    unfold truncationRationalCoefficient
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp [zero_pow hd0, zero_pow hn, hden]
  convert hc.tendsto using 1
  simp [truncationRationalCoefficient, zero_pow hd0, zero_pow hn, pow_two]

theorem truncation_rational_defect_tendsto_zero {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (truncationRationalDefect d) (𝓝 0) (𝓝 0) := by
  have hn : d - 1 ≠ 0 := by omega
  have hp : Tendsto (fun t : ℝ => t ^ (d - 1)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (d - 1)) 0 := by fun_prop
    simpa only [zero_pow hn] using hc.tendsto
  convert hp.mul (truncation_rational_coefficient_tendsto hd) using 1
  · ext t
    exact truncation_rational_defect_factor d t
  · simp

theorem truncation_rational_quotient_tendsto {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun t : ℝ => truncationRationalDefect d t / t ^ (d - 1))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((d : ℝ) * (d - 1) / (d + 1) ^ 2)) := by
  apply (truncation_rational_coefficient_tendsto hd).mono_left nhdsWithin_le_nhds
    |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [truncation_rational_defect_factor]
  have ht0 : t ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
  exact (mul_div_cancel_left₀ _ ht0).symm

theorem truncation_asymptotic_coefficient_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < (d : ℝ) * (d - 1) / (d + 1) ^ 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  positivity

#print axioms truncation_rational_defect_factor
#print axioms truncation_rational_coefficient_pos
#print axioms truncation_rational_defect_pos
#print axioms truncation_rational_coefficient_tendsto
#print axioms truncation_rational_defect_tendsto_zero
#print axioms truncation_rational_quotient_tendsto
#print axioms truncation_asymptotic_coefficient_pos

end Entry005
