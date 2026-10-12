import GaussianSliceFlux

open MeasureTheory ProbabilityTheory Set
namespace GaussianMeasureBridge
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- Restricting the base of a hypograph simply restricts its density boundary
integral. This is used for one exposed facet of a polyhedral graph. -/
theorem gaussian_masked_hypograph_flux (b : α → ℝ) (hb : Measurable b)
    (s : Set α) (hs : MeasurableSet s) :
    (∫ z in {z : α × ℝ | z.1 ∈ s ∧ z.2 < b z.1},
      z.2 ∂μ.prod (gaussianReal 0 1)) = -(∫ y in s, standardDensity (b y) ∂μ) := by
  have hr : MeasurableSet {z : α × ℝ | z.1 ∈ s ∧ z.2 < b z.1} :=
    (hs.preimage measurable_fst).inter (measurableSet_lt measurable_snd (hb.comp measurable_fst))
  have hi : Integrable (fun z : α × ℝ => z.2) (μ.prod (gaussianReal 0 1)) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).comp_snd μ
  rw [← integral_indicator hr, integral_prod _ (hi.indicator hr), ← integral_indicator hs,
    ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    by_cases hy : y ∈ s
    · have he : (fun x : ℝ => {z : α × ℝ | z.1 ∈ s ∧ z.2 < b z.1}.indicator
          (fun z => z.2) (y,x)) = (Iio (b y)).indicator (fun x => x) := by
        ext x
        by_cases hx : x < b y <;> simp [hy,hx]
      rw [he, integral_indicator measurableSet_Iio, gaussianReal_lower_halfline_firstMoment,
        Set.indicator_of_mem hy]
    · simp [hy]

end GaussianMeasureBridge
