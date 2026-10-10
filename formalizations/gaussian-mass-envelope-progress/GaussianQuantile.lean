import GaussianHazard
import Mathlib.Topology.Order.IntermediateValue

/-! The full probability-parameter version of the Gaussian hazard lemma.
Quantiles are constructed from the actual tail, its endpoint limits and IVT. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace GaussianMeasureBridge

lemma gaussianTail_continuous : Continuous gaussianTail :=
  continuous_iff_continuousAt.mpr fun a => (gaussianTail_hasDerivAt a).continuousAt

lemma gaussianTail_strictAnti : StrictAnti gaussianTail := by
  apply strictAnti_of_hasDerivAt_neg gaussianTail_hasDerivAt
  intro a
  exact neg_neg_of_pos (standardDensity_pos a)

lemma gaussianTail_tendsto_one : Tendsto gaussianTail atBot (𝓝 1) := by
  have h : Tendsto (fun a : ℝ => ∫ x in Iic a, standardDensity x) atBot (𝓝 0) :=
    tendsto_integral_Iic_zero tendsto_id
  have he : (fun a : ℝ => 1 - ∫ x in Iic a, standardDensity x) = gaussianTail := by
    funext a
    have hsum := integral_add_compl (μ := volume) (s := Ioi a)
      (f := standardDensity) measurableSet_Ioi integrable_standardDensity
    rw [compl_Ioi, show (∫ x, standardDensity x) = 1 from
      integral_gaussianPDFReal_eq_one 0 one_ne_zero] at hsum
    change gaussianTail a + _ = 1 at hsum
    linarith
  have ht := h.const_sub 1
  rw [he, sub_zero] at ht
  exact ht

/-- Every strictly interior probability is the tail at an actual, unique real threshold. -/
theorem exists_unique_gaussianTail_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃! a, gaussianTail a = p := by
  have hlo : ∀ᶠ a in atTop, gaussianTail a < p :=
    gaussianTail_tendsto_zero.eventually (gt_mem_nhds hp)
  have hhi : ∀ᶠ a in atBot, p < gaussianTail a :=
    gaussianTail_tendsto_one.eventually (lt_mem_nhds hp1)
  obtain ⟨a, ha⟩ := intermediate_value_univ₂_eventually₂ gaussianTail_continuous
    (continuous_const : Continuous (fun _ : ℝ => p))
    (hlo.mono fun _ h => h.le) (hhi.mono fun _ h => h.le)
  exact ⟨a, ha, fun b hb => gaussianTail_strictAnti.injective (hb.trans ha.symm)⟩

/-- The unique upper-tail threshold. Its value outside (0,1) is deliberately irrelevant. -/
noncomputable def upperQuantile (p : ℝ) : ℝ :=
  if hp : 0 < p ∧ p < 1 then
    Classical.choose (exists_unique_gaussianTail_eq hp.1 hp.2) else 0

lemma gaussianTail_upperQuantile {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    gaussianTail (upperQuantile p) = p := by
  unfold upperQuantile
  rw [dif_pos ⟨hp, hp1⟩]
  exact (Classical.choose_spec (exists_unique_gaussianTail_eq hp hp1)).1

lemma upperQuantile_antitone {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (hpq : p ≤ q) : upperQuantile q ≤ upperQuantile p := by
  by_contra hn
  have h := gaussianTail_strictAnti (lt_of_not_ge hn)
  rw [gaussianTail_upperQuantile hq hq1, gaussianTail_upperQuantile hp hp1] at h
  exact (not_lt_of_ge hpq) h

/-- The actual upper Gaussian hazard in the paper's probability parameter. -/
noncomputable def massHazard (p : ℝ) : ℝ := standardDensity (upperQuantile p) / p

lemma massHazard_eq_thresholdHazard {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    massHazard p = thresholdHazard (upperQuantile p) := by
  unfold massHazard thresholdHazard
  rw [gaussianTail_upperQuantile hp hp1]

/-- Lemma 2 of the mass-envelope paper, with its complete quantifiers and actual Gaussian objects. -/
theorem squared_hazard_log_lipschitz {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq1 : q < 1) :
    0 ≤ massHazard p ^ 2 - massHazard q ^ 2 ∧
    massHazard p ^ 2 - massHazard q ^ 2 ≤ 2 * Real.log (q / p) := by
  have hp1 : p < 1 := hpq.trans_lt hq1
  have hq : 0 < q := hp.trans_le hpq
  have h := squared_hazard_log_lipschitz_threshold (upperQuantile q) (upperQuantile p)
    (upperQuantile_antitone hp hp1 hq hq1 hpq)
  rwa [gaussianTail_upperQuantile hq hq1, gaussianTail_upperQuantile hp hp1,
    ← massHazard_eq_thresholdHazard hp hp1, ← massHazard_eq_thresholdHazard hq hq1] at h

end GaussianMeasureBridge
