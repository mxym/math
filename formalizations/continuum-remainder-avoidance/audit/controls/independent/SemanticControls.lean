import ContinuumRemainder.Sampling
import ContinuumRemainder.DistinctMisses
import ContinuumRemainder.ErrorDomination
import ContinuumRemainder.LogGeometry

open Set MeasureTheory ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
namespace IndependentRemainderControls

noncomputable def dyadicInputs : Set ℝ := Set.range dyadic

theorem dyadicInputs_positive : dyadicInputs ⊆ Ioi 0 := by
  rintro a ⟨n, rfl⟩
  change 0 < (1 / 2 : ℝ) ^ n
  positivity

theorem dyadicInputs_syndetic : LogSyndetic dyadicInputs := by
  refine ⟨1, 1, by omega, by omega, ?_⟩
  intro j _
  refine ⟨j, le_rfl, by omega, dyadic j, ⟨j, rfl⟩, ?_, le_rfl⟩
  unfold dyadic
  rw [pow_succ]
  have hpos : 0 < (1 / 2 : ℝ) ^ j := by positivity
  nlinarith

theorem ioi_positive_syndetic : LogSyndetic (Ioi (0 : ℝ)) := by
  obtain ⟨G, J, hG, hJ, h⟩ := dyadicInputs_syndetic
  refine ⟨G, J, hG, hJ, ?_⟩
  intro j hj
  obtain ⟨i, hi, hiG, a, ha, hab⟩ := h j hj
  exact ⟨i, hi, hiG, a, dyadicInputs_positive ha, hab⟩

theorem actual_sample_nonvacuity :
    Nonempty (SampledLogConfiguration dyadicInputs (1 / 2) 10) :=
  dyadicInputs_syndetic.exists_sampledLogConfiguration (1 / 2) (by norm_num) 10

theorem empty_not_syndetic : ¬ LogSyndetic (∅ : Set ℝ) := by
  rintro ⟨G, J, _, _, h⟩
  obtain ⟨i, _, _, a, ha, _⟩ := h J le_rfl
  exact ha

-- A genuinely nonzero remainder and a negative, nonzero leading coefficient.
noncomputable def nonlinearExample (a : ℝ) : ℝ :=
  7 - 2 * a ^ (1 / 2 : ℝ) + a ^ (5 / 6 : ℝ)

theorem nonlinearExample_remainder :
    PowerRemainderOn dyadicInputs nonlinearExample 7 (-2) (1 / 2) (1 / 3) 1 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a _ ha _
  have hexp : (1 / 2 : ℝ) + 1 / 3 = 5 / 6 := by norm_num
  rw [hexp, one_mul]
  have heq : nonlinearExample a - 7 - (-2) * a ^ (1 / 2 : ℝ) =
      a ^ (5 / 6 : ℝ) := by unfold nonlinearExample; ring
  rw [heq, abs_of_nonneg (Real.rpow_nonneg ha.le _)]

-- Without c != 0, the exact remainder condition allows a constant image.
theorem zero_coefficient_constant_remainder :
    PowerRemainderOn dyadicInputs (fun _ => 0) 0 0 1 1 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a _ _ _
  simp

-- Even with c = 1, alpha = 0 permits complete cancellation.
theorem zero_rate_constant_remainder :
    PowerRemainderOn dyadicInputs (fun _ => 0) 0 1 1 0 1 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a _ ha _
  simp [abs_of_pos ha]

-- Even with alpha = 1 and c = 1, s = 0 permits a constant image.
theorem zero_power_constant_remainder :
    PowerRemainderOn dyadicInputs (fun _ => 1) 0 1 0 1 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro a _ _ _
  simp

-- Infinitely many admissible inputs do not imply infinitely many image values.
theorem constant_tail_values_finite (A E : Set ℝ) (ρ y : ℝ) :
    (TailValuesOutside A (fun _ => y) E ρ).Finite := by
  apply (Set.finite_singleton y).subset
  rintro z ⟨a, _, _, _, hy, _⟩
  simpa only [Set.mem_singleton_iff] using hy.symm

theorem zero_coefficient_counterexample :
    LogSyndetic dyadicInputs ∧ dyadicInputs ⊆ Ioi 0 ∧
    PowerRemainderOn dyadicInputs (fun _ => 0) 0 0 1 1 0 ∧
    ¬ (TailValuesOutside dyadicInputs (fun _ => 0) ∅ 1).Infinite :=
  ⟨dyadicInputs_syndetic, dyadicInputs_positive,
    zero_coefficient_constant_remainder, (constant_tail_values_finite _ _ _ _).not_infinite⟩

theorem zero_rate_counterexample :
    LogSyndetic dyadicInputs ∧ dyadicInputs ⊆ Ioi 0 ∧
    PowerRemainderOn dyadicInputs (fun _ => 0) 0 1 1 0 1 ∧
    ¬ (TailValuesOutside dyadicInputs (fun _ => 0) ∅ 1).Infinite :=
  ⟨dyadicInputs_syndetic, dyadicInputs_positive,
    zero_rate_constant_remainder, (constant_tail_values_finite _ _ _ _).not_infinite⟩

theorem zero_power_counterexample :
    LogSyndetic dyadicInputs ∧ dyadicInputs ⊆ Ioi 0 ∧
    PowerRemainderOn dyadicInputs (fun _ => 1) 0 1 0 1 0 ∧
    ¬ (TailValuesOutside dyadicInputs (fun _ => 1) ∅ 1).Infinite :=
  ⟨dyadicInputs_syndetic, dyadicInputs_positive,
    zero_power_constant_remainder, (constant_tail_values_finite _ _ _ _).not_infinite⟩

-- Actual activation, with two inactive endpoints and an active interior point.
theorem activation_lower_excluded :
    ((⟨1, by norm_num⟩, ⟨1, by norm_num⟩) : PowerParams 1 2) ∉
      logActivation 1 0 1 2 := by norm_num [logActivation]

theorem activation_upper_excluded :
    ((⟨2, by norm_num⟩, ⟨1, by norm_num⟩) : PowerParams 1 2) ∉
      logActivation 1 0 1 2 := by norm_num [logActivation]

theorem activation_interior_included :
    ((⟨3/2, by norm_num⟩, ⟨1, by norm_num⟩) : PowerParams 1 2) ∈
      logActivation 1 0 1 2 := by norm_num [logActivation]

-- Closed equality |e|=r is safe with the doubled open buffer, for both signs.
theorem doubled_buffer_positive_endpoint :
    (1/2 : ℝ)+1 ∈ Metric.thickening 2 ({0}:Set ℝ) := by
  apply Metric.mem_thickening_iff.2
  exact ⟨0, by simp, by norm_num [Real.dist_eq]⟩

theorem doubled_buffer_negative_endpoint :
    (-1/2 : ℝ)-1 ∈ Metric.thickening 2 ({0}:Set ℝ) := by
  apply Metric.mem_thickening_iff.2
  exact ⟨0, by simp, by norm_num [Real.dist_eq]⟩

theorem single_buffer_fails :
    (1/2 : ℝ)+1 ∉ Metric.thickening 1 ({0}:Set ℝ) := by
  intro h
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 h
  have hz0 : z = 0 := by simpa using hz
  subst z
  norm_num [Real.dist_eq] at hd

-- U+k=0 is valid; q=0 still has a strictly positive safety radius.
theorem zero_shift_error_control :
    (1 : ℝ) * (1/2 : ℝ) ^ (1+1 : ℝ) < errorRadius 1 0 1 1 0 := by
  norm_num [errorRadius, Real.rpow_natCast]

theorem zero_magnitude_positive_radius : 0 < errorRadius 0 0 1 1 0 := by
  norm_num [errorRadius]

-- The two hypotheses on active-error domination are not removable.
theorem exponent_upper_bound_essential :
    ¬ ((1 : ℝ) * (1/4 : ℝ) ^ (2+4 : ℝ) ≤ errorRadius 1 0 4 1 3) := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]

theorem nonnegative_output_shift_essential :
    ¬ ((1 : ℝ) * (4 : ℝ) ^ (1+6 : ℝ) ≤ errorRadius 1 0 6 3 (-3)) := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]

-- For a family chosen from E, all identity-shift values stay inside E.
def adaptiveInputs (E : Set ℝ) (y : ℝ) : Set ℝ :=
  {a | 0 < a ∧ y + a ∈ E}

theorem adaptive_family_defeats_avoidance (E : Set ℝ) (y : ℝ)
    (_hA : LogSyndetic (adaptiveInputs E y)) :
    ¬ AvoidsPowerRemainderTails (fun _ : Unit => adaptiveInputs E y) E := by
  intro h
  have hf : PowerRemainderOn (adaptiveInputs E y) (fun a => y+a) y 1 1 1 0 := by
    refine ⟨1, by norm_num, ?_⟩
    intro a _ _ _
    simp [Real.rpow_one]
  have hinf := h () 1 1 y 1 0 (fun a => y+a)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf 1 (by norm_num)
  have hempty : TailValuesOutside (adaptiveInputs E y) (fun a => y+a) E 1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro z ⟨a, ha, _, _, hza, hz⟩
    exact hz (hza ▸ ha.2)
  rw [hempty] at hinf
  exact hinf Set.finite_empty

#print axioms dyadicInputs_syndetic
#print axioms actual_sample_nonvacuity
#print axioms zero_coefficient_counterexample
#print axioms zero_rate_counterexample
#print axioms zero_power_counterexample
#print axioms adaptive_family_defeats_avoidance
end IndependentRemainderControls
