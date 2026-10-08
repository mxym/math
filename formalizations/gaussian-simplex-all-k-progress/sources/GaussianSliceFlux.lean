import GaussianHalflineFlux
import Mathlib.MeasureTheory.Integral.Prod

/-! Gaussian flux by one-dimensional slicing. These are integral identities for
actual measurable regions, with no boundary regularity assumption. The upper
and lower graph identities are the analytic primitives for polyhedral slices. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianMeasureBridge

theorem gaussianReal_lower_halfline_firstMoment (a : ℝ) :
    (∫ x in Iio a, x ∂gaussianReal 0 1) = -standardDensity a := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) (by norm_num : (1 : NNReal) ≠ 0)
  have h := integral_add_compl (μ := gaussianReal 0 1) (s := Ioi a) (f := fun x : ℝ => x) measurableSet_Ioi
    (IsGaussian.integrable_id (μ := gaussianReal 0 1))
  rw [compl_Ioi, integral_Iic_eq_integral_Iio, integral_id_gaussianReal,
    gaussianReal_halfline_firstMoment] at h
  linarith

theorem gaussianReal_interval_firstMoment (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Ioo a b, x ∂gaussianReal 0 1) = standardDensity a - standardDensity b := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) (by norm_num : (1 : NNReal) ≠ 0)
  have h := setIntegral_sdiff (μ := gaussianReal 0 1) (f := fun x : ℝ => x)
    (s := Ioi a) (t := Ioi b) measurableSet_Ioi
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).integrableOn
    (fun _ hx => lt_of_le_of_lt hab hx)
  rw [Ioi_sdiff_Ioi, integral_Ioc_eq_integral_Ioo,
    gaussianReal_halfline_firstMoment, gaussianReal_halfline_firstMoment] at h
  exact h

section Product
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- A measurable epigraph has an exact inward coordinate-flux formula. The
base measure need only be finite; in applications it is a Gaussian marginal. -/
theorem gaussian_epigraph_coordinate_flux (a : α → ℝ) (ha : Measurable a) :
    (∫ z in {z : α × ℝ | a z.1 < z.2}, z.2 ∂μ.prod (gaussianReal 0 1)) =
      ∫ y, standardDensity (a y) ∂μ := by
  have hs : MeasurableSet {z : α × ℝ | a z.1 < z.2} :=
    measurableSet_lt (ha.comp measurable_fst) measurable_snd
  have hi : Integrable (fun z : α × ℝ => z.2) (μ.prod (gaussianReal 0 1)) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd μ
  rw [← integral_indicator hs, integral_prod _ (hi.indicator hs)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    have he : (fun x : ℝ => {z : α × ℝ | a z.1 < z.2}.indicator
        (fun z => z.2) (y,x)) = (Ioi (a y)).indicator (fun x => x) := by
      ext x
      by_cases hx : a y < x <;> simp [hx]
    rw [he, integral_indicator measurableSet_Ioi, gaussianReal_halfline_firstMoment]

theorem gaussian_hypograph_coordinate_flux (b : α → ℝ) (hb : Measurable b) :
    (∫ z in {z : α × ℝ | z.2 < b z.1}, z.2 ∂μ.prod (gaussianReal 0 1)) =
      -(∫ y, standardDensity (b y) ∂μ) := by
  have hs : MeasurableSet {z : α × ℝ | z.2 < b z.1} :=
    measurableSet_lt measurable_snd (hb.comp measurable_fst)
  have hi : Integrable (fun z : α × ℝ => z.2) (μ.prod (gaussianReal 0 1)) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd μ
  rw [← integral_indicator hs, integral_prod _ (hi.indicator hs), ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    have he : (fun x : ℝ => {z : α × ℝ | z.2 < b z.1}.indicator
        (fun z => z.2) (y,x)) = (Iio (b y)).indicator (fun x => x) := by
      ext x
      by_cases hx : x < b y <;> simp [hx]
    rw [he, integral_indicator measurableSet_Iio, gaussianReal_lower_halfline_firstMoment]

/-- The two graph contributions to flux through a variable strip. Strict or
closed endpoints have the same Gaussian integral. -/
theorem gaussian_strip_coordinate_flux (a b : α → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hab : ∀ᵐ y ∂μ, a y ≤ b y) :
    (∫ z in {z : α × ℝ | a z.1 < z.2 ∧ z.2 < b z.1},
      z.2 ∂μ.prod (gaussianReal 0 1)) =
      ∫ y, standardDensity (a y) - standardDensity (b y) ∂μ := by
  have hs : MeasurableSet {z : α × ℝ | a z.1 < z.2 ∧ z.2 < b z.1} :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hb.comp measurable_fst))
  have hi : Integrable (fun z : α × ℝ => z.2) (μ.prod (gaussianReal 0 1)) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd μ
  rw [← integral_indicator hs, integral_prod _ (hi.indicator hs)]
  apply integral_congr_ae
  filter_upwards [hab] with y hy
  have he : (fun x : ℝ => {z : α × ℝ | a z.1 < z.2 ∧ z.2 < b z.1}.indicator
      (fun z => z.2) (y,x)) = (Ioo (a y) (b y)).indicator (fun x => x) := by
    ext x
    by_cases hx : a y < x ∧ x < b y <;> simp [hx]
  rw [he, integral_indicator measurableSet_Ioo, gaussianReal_interval_firstMoment _ _ hy]

end Product
end GaussianMeasureBridge
