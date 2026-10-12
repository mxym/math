import SemanticControls
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

open Set Filter Topology MeasureTheory ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
namespace IndependentRemainderControls

-- A right dyadic shell must be occupied whenever the centered density exceeds 3/4.
theorem occupied_shell_of_density (E : Set ℝ) (y r : ℝ) (hr : 0 < r)
    (hden : ENNReal.ofReal (3/4 : ℝ) <
      volume (E ∩ Metric.closedBall y r) / volume (Metric.closedBall y r)) :
    (E ∩ Ioc (y+r/2) (y+r)).Nonempty := by
  by_contra hn
  have hsub : E ∩ Metric.closedBall y r ⊆ Icc (y-r) (y+r/2) := by
    intro z hz
    rw [Real.closedBall_eq_Icc] at hz
    refine ⟨hz.2.1, ?_⟩
    by_contra hhi
    apply hn
    exact ⟨z, hz.1, lt_of_not_ge hhi, hz.2.2⟩
  have hμ := ENNReal.div_le_div_right (show volume (E ∩ Metric.closedBall y r) ≤ volume (Icc (y-r) (y+r/2)) from measure_mono hsub) (volume (Metric.closedBall y r))
  rw [Real.volume_closedBall, Real.volume_Icc] at hμ
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2*r)] at hμ
  have heq : (y+r/2-(y-r))/(2*r) = (3/4:ℝ) := by field_simp; ring
  rw [heq] at hμ
  exact (not_lt_of_ge hμ) (by simpa only [Real.volume_closedBall] using hden)

-- At a Lebesgue density point every sufficiently small dyadic shell is occupied.
theorem density_point_gives_adaptive_syndetic (E : Set ℝ) (y : ℝ)
    (hden : Tendsto (fun r => volume (E ∩ Metric.closedBall y r) /
      volume (Metric.closedBall y r)) (𝓝[>] 0) (𝓝 1)) :
    LogSyndetic (adaptiveInputs E y) := by
  have hdy : Tendsto dyadic atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    · exact Filter.Eventually.of_forall (fun n => by change 0 < (1/2:ℝ)^n; positivity)
  have hev : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (3/4:ℝ) <
      volume (E ∩ Metric.closedBall y (dyadic j)) / volume (Metric.closedBall y (dyadic j)) :=
    (hden.comp hdy).eventually (lt_mem_nhds (by norm_num))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  refine ⟨1, J+1, by omega, by omega, ?_⟩
  intro j hj
  obtain ⟨b, hbE, hbLower, hbUpper⟩ := occupied_shell_of_density E y (dyadic j)
    (by unfold dyadic; positivity) (hJ j (by omega))
  have hd : dyadic (j+1) = dyadic j / 2 := by unfold dyadic; rw [pow_succ]; ring
  have hdpos : 0 < dyadic j := by unfold dyadic; positivity
  refine ⟨j, le_rfl, by omega, b-y, ?_, ?_, ?_⟩
  · change 0 < b-y ∧ y+(b-y) ∈ E
    exact ⟨by linarith, by convert hbE using 1; ring⟩
  · rw [hd]
    linarith
  · linarith

-- The family-first quantifier is essential for EVERY positive-measure E,
-- including closed nowhere-dense periodic sets allowed by the target.
theorem no_positive_measure_universal_family (E : Set ℝ) (hE : volume E ≠ 0) :
    ∃ A : Set ℝ, A ⊆ Ioi 0 ∧ LogSyndetic A ∧
      ¬ AvoidsPowerRemainderTails (fun _ : Unit => A) E := by
  obtain ⟨y, _hy, hd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE
    (Besicovitch.ae_tendsto_measure_inter_div volume E)
  have hA := density_point_gives_adaptive_syndetic E y hd
  exact ⟨adaptiveInputs E y, fun _ ha => ha.1, hA,
    adaptive_family_defeats_avoidance E y hA⟩

#print axioms no_positive_measure_universal_family
end IndependentRemainderControls
