import ContinuumRemainder.ErrorSchedule
import ContinuumRemainder.RobustAssembly

/-!
Exact countercontrols for hypotheses and buffer conventions used in sections
6--7. These are kernel proofs, not floating evaluations or sampled exponents.
-/
namespace ContinuumRemainder

open Set ContinuumGeometric

/-- Without a positive remainder exponent, the actual buffer cost cannot vanish. -/
theorem zero_alpha_buffer_cost_ge (q : ℕ) (k : ℤ) (s₁ : ℝ) (U T : ℕ) :
    16 ≤ 4 * ((2 ^ (U + T + 2) : ℕ) : ℝ) * errorRadius q k 0 s₁ U := by
  rw [actual_buffer_cost_eq]
  simp only [zero_mul, zero_div, sub_zero]
  have hcoeff : (1 : ℝ) ≤ (q : ℝ) * (2 : ℝ) ^ (-k) + 1 := by
    have h : (0 : ℝ) ≤ (q : ℝ) * (2 : ℝ) ^ (-k) := by positivity
    linarith
  have hpower : (16 : ℝ) ≤ (2 : ℝ) ^ ((T : ℝ) + 4) := by
    rw [show (T : ℝ) + 4 = ((T + 4 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_add]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ T := one_le_pow₀ (by norm_num)
    norm_num at *
    nlinarith
  nlinarith

/-- Activation alone cannot justify replacing an unbounded s by a fixed s₁. -/
theorem exponent_upper_bound_needed :
    (3 : ℝ) < 2 * 2 ∧
      errorRadius 1 0 4 1 3 < (1 : ℝ) * (1 / 4 : ℝ) ^ (2 + 4 : ℝ) := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]

/-- The nonnegative U+k hypothesis is needed when deriving z from s≤s₁. -/
theorem nonnegative_output_shift_needed :
    (-3 : ℝ) < 1 * (-2) ∧
      errorRadius 1 0 6 3 (-3) < (1 : ℝ) * (4 : ℝ) ^ (1 + 6 : ℝ) := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]

/-- Equality in the allowed error is safe with the outer doubled OPEN buffer. -/
theorem allowed_error_endpoint_is_safe :
    (1 / 2 : ℝ) + 1 ∈ Metric.thickening 2 ({0} : Set ℝ) := by
  have hz : (1 / 2 : ℝ) ∈ Metric.thickening 1 ({0} : Set ℝ) := by
    apply Metric.mem_thickening_iff.2
    refine ⟨0, by simp, ?_⟩
    norm_num [Real.dist_eq]
  simpa only [mul_one] using
    double_buffer_contains_perturbation ({0} : Set ℝ) 1 (1 / 2) 1 hz (by norm_num)

/-- Keeping only the inner buffer fails for that same endpoint-sized error. -/
theorem single_buffer_endpoint_fails :
    (1 / 2 : ℝ) + 1 ∉ Metric.thickening 1 ({0} : Set ℝ) := by
  intro h
  obtain ⟨b, hb, hdist⟩ := Metric.mem_thickening_iff.1 h
  have hb0 : b = 0 := by simpa using hb
  subst b
  norm_num [Real.dist_eq] at hdist

end ContinuumRemainder
