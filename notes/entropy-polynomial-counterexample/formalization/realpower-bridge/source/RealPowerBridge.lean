import Counterexample

/-!
# The original real-power parameter definition

An additive bridge from equation (1.1) to the already verified integer-power
parameter equation for k = 11, r = 10. The five original proof modules are
unchanged. Every use of a real power has an explicitly real exponent.
-/

set_option autoImplicit false

namespace EntropyCounterexample

/-- On the positive real domain, the original real-power definition is equivalent
    to the integer-power equation at the counterexample pair `(11,10)`. -/
theorem parameter_equation_iff_original_real_power {a : ℝ} (ha : 0 < a) :
    a^10 * (1+a) = 1 ↔ a = 1 / Real.rpow (1+a) ((11 : ℝ)/10-1) := by
  have hb : 0 < 1+a := by linarith
  have he : ((11 : ℝ)/10-1) = (10 : ℝ)⁻¹ := by norm_num
  rw [he]
  simp only [Real.rpow_eq_pow]
  have hr : (1+a) ^ ((10 : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  have hc1 : (a^10) ^ ((10 : ℝ)⁻¹) = a := by
    simpa using Real.pow_rpow_inv_natCast ha.le (by norm_num : (10 : ℕ) ≠ 0)
  have hc2 : ((1+a) ^ ((10 : ℝ)⁻¹)) ^ (10 : ℕ) = 1+a := by
    simpa using Real.rpow_inv_natCast_pow hb.le (by norm_num : (10 : ℕ) ≠ 0)
  constructor
  · intro h
    have hroot := congrArg (fun t : ℝ => t ^ ((10 : ℝ)⁻¹)) h
    rw [Real.mul_rpow (pow_nonneg ha.le 10) hb.le,
      hc1, Real.one_rpow] at hroot
    exact (eq_div_iff hr).2 hroot
  · intro h
    have hmul : a * (1+a) ^ ((10 : ℝ)⁻¹) = 1 := (eq_div_iff hr).1 h
    have hpow := congrArg (fun t : ℝ => t^10) hmul
    rw [mul_pow, hc2, one_pow] at hpow
    exact hpow

/-- The constructed exact parameter satisfies equation (1.1), with real powers. -/
theorem alpha_original_real_power :
    alpha = 1 / Real.rpow (1+alpha) ((11 : ℝ)/10-1) :=
  (parameter_equation_iff_original_real_power alpha_pos).mp alpha_equation

/-- The original real-power definition has a unique solution in `(0,1)`. -/
theorem alpha_existsUnique_original_real_power :
    ∃! a : ℝ, a ∈ Set.Ioo 0 1 ∧
      a = 1 / Real.rpow (1+a) ((11 : ℝ)/10-1) := by
  refine ⟨alpha, ⟨⟨alpha_pos, alpha_lt_one⟩, alpha_original_real_power⟩, ?_⟩
  intro a ha
  exact alpha_unique ha.1.1
    ((parameter_equation_iff_original_real_power ha.1.1).mpr ha.2)

/-- The counterexample works for any parameter given directly by equation (1.1). -/
theorem counterexample_original_real_power {a : ℝ}
    (ha : a ∈ Set.Ioo 0 1)
    (heq : a = 1 / Real.rpow (1+a) ((11 : ℝ)/10-1)) :
    4 ≤ unitRootCount (pPolynomial 11 10 a) :=
  counterexample_for_any_parameter ha
    ((parameter_equation_iff_original_real_power ha.1).mpr heq)

/-- A complete counterexample using the paper's original real-power parameter definition. -/
theorem counterexample_to_conjecture_two_original_real_power :
    ∃ k r : ℕ, ∃ a : ℝ,
      0 < r ∧ r < k ∧ Nat.Coprime k r ∧ a ∈ Set.Ioo 0 1 ∧
      a = 1 / Real.rpow (1+a) ((k : ℝ)/r-1) ∧
      4 ≤ unitRootCount (pPolynomial k r a) := by
  refine ⟨11, 10, alpha, by norm_num, by norm_num, by decide,
    ⟨alpha_pos, alpha_lt_one⟩, ?_, counterexample_root_count⟩
  exact alpha_original_real_power

/-- The two-root conjecture fails with the parameter expressed by equation (1.1). -/
theorem wakhare_conjecture_two_false_original_real_power :
    ¬ (∀ k r : ℕ, 0 < r → r < k → Nat.Coprime k r →
      ∀ a : ℝ, a ∈ Set.Ioo 0 1 →
        a = 1 / Real.rpow (1+a) ((k : ℝ)/r-1) →
        unitRootCount (pPolynomial k r a) = 2) := by
  intro hc
  apply counterexample_not_two
  exact hc 11 10 (by norm_num) (by norm_num) (by decide) alpha
    ⟨alpha_pos, alpha_lt_one⟩ alpha_original_real_power

end EntropyCounterexample
