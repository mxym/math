import Entry005.TruncationRationalDefect

/-!
The scalar analytic part of actual truncation sharpness. The final theorem
accepts an explicit equality between a supplied function and equation (D).
It proves no geometric equality, maximum-simplex fact, or centroid identity.
-/

noncomputable section

open Filter Topology

namespace Entry005

theorem truncation_power_exponent_pos {d : ℕ} (hd : 3 ≤ d)
    {α : ℝ} (hα : 1 / ((d - 1 : ℕ) : ℝ) < α) :
    0 < α ∧ 0 < ((d - 1 : ℕ) : ℝ) * α - 1 := by
  have hn : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have ha : 0 < α := lt_trans (div_pos zero_lt_one hn) hα
  have hb : 1 < α * ((d - 1 : ℕ) : ℝ) := (div_lt_iff₀ hn).mp hα
  exact ⟨ha, by nlinarith⟩

theorem truncation_rational_power_ratio_tendsto_zero {d : ℕ} (hd : 3 ≤ d)
    {α : ℝ} (hα : 1 / ((d - 1 : ℕ) : ℝ) < α) (C : ℝ) :
    Tendsto (fun t : ℝ => C * (truncationRationalDefect d t) ^ α / ((d + 1) * t))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  obtain ⟨ha, hb⟩ := truncation_power_exponent_pos hd hα
  have hc : Tendsto (fun t : ℝ => (truncationRationalCoefficient d t) ^ α)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (((d : ℝ) * (d - 1) / (d + 1) ^ 2) ^ α)) :=
    ((truncation_rational_coefficient_tendsto hd).mono_left nhdsWithin_le_nhds).rpow_const
      (Or.inr ha.le)
  have hp : Tendsto (fun t : ℝ => t ^ (((d - 1 : ℕ) : ℝ) * α - 1))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioi 0] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact hid.rpow_const_nhds_zero hb
  have hprod := (hc.const_mul (C / ((d : ℝ) + 1))).mul hp
  simp only [mul_zero] at hprod
  apply hprod.congr'
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  have hcp := truncation_rational_coefficient_pos hd ht ht1
  rw [truncation_rational_defect_factor,
    Real.mul_rpow (pow_nonneg ht.le _) hcp.le,
    ← Real.rpow_natCast_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem truncation_rational_power_obstruction {d : ℕ} (hd : 3 ≤ d)
    {α : ℝ} (hα : 1 / ((d - 1 : ℕ) : ℝ) < α)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < min ε 1 ∧
      0 < truncationRationalDefect d t ∧ truncationRationalDefect d t < ε ∧
      C * (truncationRationalDefect d t) ^ α < (d + 1) * t := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t < min ε 1 :=
    (eventually_lt_nhds (lt_min hε zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, truncationRationalDefect d t < ε :=
    ((truncation_rational_defect_tendsto_zero hd).mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hε)
  have hr : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0,
      C * (truncationRationalDefect d t) ^ α / ((d + 1) * t) < 1 :=
    (truncation_rational_power_ratio_tendsto_zero hd hα C).eventually
      (eventually_lt_nhds zero_lt_one)
  have hall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0,
      0 < t ∧ t < min ε 1 ∧
        0 < truncationRationalDefect d t ∧ truncationRationalDefect d t < ε ∧
        C * (truncationRationalDefect d t) ^ α < (d + 1) * t := by
    filter_upwards [self_mem_nhdsWithin, hsmall, he, hr] with t ht htε het hrt
    have ht1 := lt_of_lt_of_le htε (min_le_right ε 1)
    have hden : 0 < ((d : ℝ) + 1) * t :=
      mul_pos (by positivity) ht
    exact ⟨ht, htε, truncation_rational_defect_pos hd ht ht1, het,
      (div_lt_one hden).mp hrt⟩
  exact hall.exists

/-- Conditional scalar assembly: `e` can be the actual geometric defect only
after the displayed pointwise equality has been proved from actual geometry.
The conclusion supplies exactly the parameter, positivity, smallness, and
power comparison needed by the geometric sharpness assembly. -/
theorem truncation_conditional_scalar_power_obstruction {d : ℕ} (hd : 3 ≤ d)
    (e : ℝ → ℝ)
    (he : ∀ t : ℝ, 0 < t → t < 1 → e t = truncationRationalDefect d t)
    {α : ℝ} (hα : 1 / ((d - 1 : ℕ) : ℝ) < α)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < min ε 1 ∧ 0 < e t ∧ e t < ε ∧
      C * (e t) ^ α < (d + 1) * t := by
  obtain ⟨t, ht, htε, hp, hs, hb⟩ := truncation_rational_power_obstruction hd hα C hε
  have ht1 := lt_of_lt_of_le htε (min_le_right ε 1)
  exact ⟨t, ht, htε, by simpa only [he t ht ht1] using hp,
    by simpa only [he t ht ht1] using hs, by simpa only [he t ht ht1] using hb⟩

/-- The exact asymptotic for a supplied function, explicitly conditional on
its equality with the rational expression on the positive parameter interval. -/
theorem truncation_conditional_scalar_quotient_tendsto {d : ℕ} (hd : 3 ≤ d)
    (e : ℝ → ℝ)
    (he : ∀ t : ℝ, 0 < t → t < 1 → e t = truncationRationalDefect d t) :
    Tendsto (fun t : ℝ => e t / t ^ (d - 1))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((d : ℝ) * (d - 1) / (d + 1) ^ 2)) := by
  apply (truncation_rational_quotient_tendsto hd).congr'
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  rw [he t ht ht1]

#print axioms truncation_power_exponent_pos
#print axioms truncation_rational_power_ratio_tendsto_zero
#print axioms truncation_rational_power_obstruction
#print axioms truncation_conditional_scalar_power_obstruction
#print axioms truncation_conditional_scalar_quotient_tendsto

end Entry005
