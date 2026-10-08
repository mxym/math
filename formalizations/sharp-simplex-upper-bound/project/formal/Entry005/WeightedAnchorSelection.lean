import Entry005.AnchorSelection
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! First absolute-moment anchor selection using the actual normalized
volume density. The ratio is integrated under the tilted law. -/

noncomputable section
open MeasureTheory

namespace Entry005

variable {α : Type*} [MeasurableSpace α]

def volumeWeightedLaw (μ : Measure α) (V : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (V x / (∫ y, V y ∂μ)))

theorem volume_weighted_law_probability (μ : Measure α) {V : α → ℝ}
    (_hmV : Measurable V) (hiV : Integrable V μ) (hV0 : ∀ x, 0 ≤ V x)
    (hB : 0 < ∫ x, V x ∂μ) : IsProbabilityMeasure (volumeWeightedLaw μ V) := by
  apply isProbabilityMeasure_iff.mpr
  unfold volumeWeightedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hiV.div_const _) (
      Filter.Eventually.of_forall (fun x => div_nonneg (hV0 x) hB.le)),
    integral_div, div_self hB.ne', ENNReal.ofReal_one]

theorem volume_weighted_law_ae_good (μ : Measure α) {V : α → ℝ}
    (hmV : Measurable V) (hB : 0 < ∫ x, V x ∂μ) {G : α → Prop}
    (hG : ∀ᵐ x ∂μ, G x) :
    ∀ᵐ x ∂volumeWeightedLaw μ V, G x ∧ 0 < V x := by
  apply (ae_withDensity_iff (hmV.div_const _).ennreal_ofReal).2
  filter_upwards [hG] with x hx hd
  refine ⟨hx, ?_⟩
  have hp : 0 < V x / (∫ y, V y ∂μ) :=
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hd)
  have heq : (V x / (∫ y, V y ∂μ)) * (∫ y, V y ∂μ) = V x := div_mul_cancel₀ _ hB.ne'
  rw [← heq]
  exact mul_pos hp hB

omit [MeasurableSpace α] in
theorem volume_weighted_density_mul_ratio {V H : α → ℝ} {B : ℝ}
    (hB : 0 < B) (hV0 : ∀ x, 0 ≤ V x) (x : α) :
    (ENNReal.ofReal (V x / B)).toReal * (H x / V x) =
      {y | V y ≠ 0}.indicator (fun y => H y / B) x := by
  rw [ENNReal.toReal_ofReal (div_nonneg (hV0 x) hB.le)]
  by_cases hx : V x = 0
  · simp [hx]
  · rw [Set.indicator_of_mem hx]
    field_simp

theorem volume_weighted_ratio_integrable (μ : Measure α) {V H : α → ℝ}
    (hmV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hiH : Integrable H μ)
    (hB : 0 < ∫ x, V x ∂μ) :
    Integrable (fun x => H x / V x) (volumeWeightedLaw μ V) := by
  unfold volumeWeightedLaw
  apply (integrable_withDensity_iff_integrable_smul' (hmV.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  have hset : MeasurableSet {x | V x ≠ 0} := (hmV (measurableSet_singleton 0)).compl
  have hi := (hiH.div_const (∫ x, V x ∂μ)).indicator hset
  apply hi.congr
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [smul_eq_mul] using (volume_weighted_density_mul_ratio hB hV0 x).symm)

theorem volume_weighted_ratio_integral_eq (μ : Measure α) {V H : α → ℝ}
    (hmV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (hB : 0 < ∫ x, V x ∂μ) :
    (∫ x, H x / V x ∂volumeWeightedLaw μ V) =
      ∫ x, {y | V y ≠ 0}.indicator (fun y => H y / (∫ z, V z ∂μ)) x ∂μ := by
  unfold volumeWeightedLaw
  rw [integral_withDensity_eq_integral_toReal_smul (hmV.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [smul_eq_mul] using volume_weighted_density_mul_ratio hB hV0 x)

theorem volume_weighted_ratio_integral_le (μ : Measure α) {V H : α → ℝ}
    (hmV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hiH : Integrable H μ)
    (hH0 : ∀ x, 0 ≤ H x) (hB : 0 < ∫ x, V x ∂μ) :
    (∫ x, H x / V x ∂volumeWeightedLaw μ V) ≤
      (∫ x, H x ∂μ) / (∫ x, V x ∂μ) := by
  rw [volume_weighted_ratio_integral_eq μ hmV hV0 hB, ← integral_div]
  have hset : MeasurableSet {x | V x ≠ 0} := (hmV (measurableSet_singleton 0)).compl
  apply integral_mono ((hiH.div_const _).indicator hset) (hiH.div_const _)
  intro x
  by_cases hx : V x ≠ 0
  · simp [hx]
  · rw [Set.indicator_of_notMem (show x ∉ {y | V y ≠ 0} from hx)]
    exact div_nonneg (hH0 x) hB.le

theorem volume_weighted_selection (μ : Measure α) {V H : α → ℝ}
    (hmV : Measurable V) (hiV : Integrable V μ) (hV0 : ∀ x, 0 ≤ V x)
    (hiH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x) {G : α → Prop}
    (hG : ∀ᵐ x ∂μ, G x) (hB : 0 < ∫ x, V x ∂μ) {K : ℝ}
    (hbudget : (∫ x, H x ∂μ) ≤ K) :
    ∃ x, G x ∧ 0 < V x ∧ H x / V x ≤ K / (∫ y, V y ∂μ) := by
  let := volume_weighted_law_probability μ hmV hiV hV0 hB
  have hgood := volume_weighted_law_ae_good μ hmV hB hG
  have hnull : volumeWeightedLaw μ V {x | ¬(G x ∧ 0 < V x)} = 0 := ae_iff.mp hgood
  obtain ⟨x, hx, hlow⟩ := exists_notMem_null_le_integral
    (volume_weighted_ratio_integrable μ hmV hV0 hiH hB) hnull
  have hxgood : G x ∧ 0 < V x := by simpa only [Set.mem_ofPred_eq, not_not] using hx
  refine ⟨x, hxgood.1, hxgood.2, hlow.trans ?_⟩
  exact (volume_weighted_ratio_integral_le μ hmV hV0 hiH hH0 hB).trans
    (div_le_div_of_nonneg_right hbudget hB.le)

end Entry005
