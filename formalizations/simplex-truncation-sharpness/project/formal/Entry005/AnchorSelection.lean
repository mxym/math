import Entry005.IntegratedWitness
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.FieldSimp

/-! Conditional anchor selection on a genuine measurable probability space.
The event probability is proved from a bounded second moment, rather than
assumed as an additional cap or anchor conclusion.
-/

noncomputable section
open MeasureTheory

namespace Entry005

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem second_moment_event_lower {V : α → ℝ} (hV : Measurable V)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ x ∂μ, 0 ≤ V x) (hVC : ∀ᵐ x ∂μ, V x ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ x, (V x) ^ 2 ∂μ) :
    v ^ 2 / C ^ 2 ≤ (μ {x | v ≤ V x}).toReal := by
  let s : Set α := {x | v ≤ V x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hV
  have hsq : Integrable (fun x => V x ^ 2) μ :=
    Integrable.mono' (integrable_const (C ^ 2))
      ((hV.pow_const 2).aestronglyMeasurable) (by
        filter_upwards [hV0, hVC] with x hx0 hxC
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith)
  have hind : Integrable (s.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hs
  have hbound : ∀ᵐ x ∂μ, V x ^ 2 ≤ v ^ 2 + C ^ 2 * s.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hV0, hVC] with x hx0 hxC
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      nlinarith [sq_nonneg v]
    · rw [Set.indicator_of_notMem hx]
      have hx' : V x < v := lt_of_not_ge hx
      nlinarith
  have h := integral_mono_ae hsq ((integrable_const _).add (hind.const_mul _)) hbound
  change (∫ x, V x ^ 2 ∂μ) ≤
    (∫ x, v ^ 2 + C ^ 2 * s.indicator (fun _ => (1 : ℝ)) x ∂μ) at h
  have hindint : (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ) = (μ s).toReal := by
    simpa [Measure.real] using integral_indicator_const (1 : ℝ) hs
  rw [integral_add (integrable_const _) (hind.const_mul _),
    integral_const_mul, hindint] at h
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
  apply (div_le_iff₀ (sq_pos_of_pos hC)).2
  nlinarith

theorem exists_well_conditioned_low_witness {V H : α → ℝ}
    (hV : Measurable V) {v C B : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ x ∂μ, 0 ≤ V x) (hVC : ∀ᵐ x ∂μ, V x ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ x, V x ^ 2 ∂μ)
    (hH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x)
    (hmean : (∫ x, H x ∂μ) ≤ B) :
    ∃ x, v ≤ V x ∧ H x ≤ B * C ^ 2 / v ^ 2 := by
  obtain ⟨x, hx, hlow⟩ := exists_conditioned_low_witness hH hH0
    (div_pos (sq_pos_of_pos hv) (sq_pos_of_pos hC))
    (second_moment_event_lower hV hv hC hV0 hVC hmoment) hmean
  refine ⟨x, hx, ?_⟩
  convert hlow using 1
  field_simp

theorem exists_well_conditioned_low_witness_ae_good {V H : α → ℝ}
    (hV : Measurable V) {v C B : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ x ∂μ, 0 ≤ V x) (hVC : ∀ᵐ x ∂μ, V x ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ x, V x ^ 2 ∂μ)
    (hH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x) {G : α → Prop}
    (hG : ∀ᵐ x ∂μ, G x) (hmean : (∫ x, H x ∂μ) ≤ B) :
    ∃ x, G x ∧ v ≤ V x ∧ H x ≤ B * C ^ 2 / v ^ 2 := by
  obtain ⟨x, hx, hxG, hlow⟩ := exists_conditioned_low_witness_ae_good hH hH0 hG
    (div_pos (sq_pos_of_pos hv) (sq_pos_of_pos hC))
    (second_moment_event_lower hV hv hC hV0 hVC hmoment) hmean
  refine ⟨x, hxG, hx, ?_⟩
  convert hlow using 1
  field_simp

theorem exists_well_conditioned_low_witness_in_support
    [TopologicalSpace α] [HereditarilyLindelofSpace α] {V H : α → ℝ}
    (hV : Measurable V) {v C B : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hV0 : ∀ᵐ x ∂μ, 0 ≤ V x) (hVC : ∀ᵐ x ∂μ, V x ≤ C)
    (hmoment : 2 * v ^ 2 ≤ ∫ x, V x ^ 2 ∂μ)
    (hH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x)
    (hmean : (∫ x, H x ∂μ) ≤ B) :
    ∃ x ∈ μ.support, v ≤ V x ∧ H x ≤ B * C ^ 2 / v ^ 2 := by
  exact exists_well_conditioned_low_witness_ae_good hV hv hC hV0 hVC hmoment
    hH hH0 μ.support_mem_ae hmean

end Entry005
