import BapatEmpiricalCloud

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section
variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]

/-- Uniform convergence of moving tests is compatible with empirical convergence,
including along any index sequence tending to infinity. -/
theorem tendsto_empirical_moving_test (μ : Measure K) [IsProbabilityMeasure μ]
    (u : ℕ → K)
    (hu : ∀ f : C(K, ℝ), Tendsto (fun n => empiricalAverage u n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (f : ℕ → C(K, ℝ)) (g : C(K, ℝ)) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => empiricalAverage u (a n) (f n)) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ := tendsto_iff_dist_tendsto_zero.mp hf
  have h₂ := tendsto_iff_dist_tendsto_zero.mp ((hu g).comp ha)
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (dist_triangle _ (empiricalAverage u (a n) g) _).trans
      (add_le_add (empiricalAverage_dist_le u (a n) (f n) g) (le_refl _)))
  simpa using h₁.add h₂

variable {T : Type*} [MetricSpace T]

/-- A continuous joint test is uniform in the compact row variable. -/
theorem tendsto_empirical_moving_parameter (μ : Measure K) [IsProbabilityMeasure μ]
    (u : ℕ → K)
    (hu : ∀ f : C(K, ℝ), Tendsto (fun n => empiricalAverage u n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (φ : K × T → ℝ) (hφ : Continuous φ)
    (t : ℕ → T) (t₀ : T) (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n => empiricalAverage u (a n) (fun x => φ (x, t n))) atTop
      (𝓝 (∫ x, φ (x, t₀) ∂μ)) := by
  let F : T → C(K, ℝ) := fun t => ⟨fun x => φ (x, t),
    hφ.comp (continuous_id.prodMk continuous_const)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hφ.comp continuous_swap
  exact tendsto_empirical_moving_test μ u hu a ha (F ∘ t) (F t₀) ((hF.tendsto t₀).comp ht)

/-- Compact continuous families preserving the limiting probability measure preserve
empirical equidistribution even when the parameter changes with the cloud size. -/
theorem moving_measurePreserving_cloud [CompactSpace T]
    (μ : Measure K) [IsProbabilityMeasure μ] (u : ℕ → K)
    (hu : ∀ f : C(K, ℝ), Tendsto (fun n => empiricalAverage u n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (A : T → K → K) (hA : Continuous (fun z : T × K => A z.1 z.2))
    (hm : ∀ t, MeasurePreserving (A t) μ μ) (t : ℕ → T) (f : C(K, ℝ)) :
    Tendsto (fun n => empiricalAverage u n (fun x => f (A (t n) x))) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨t₀, ms, hms, ht⟩ := CompactSpace.tendsto_subseq (t ∘ ns)
  refine ⟨ms, ?_⟩
  have h := tendsto_empirical_moving_parameter μ u hu (ns ∘ ms) (hns.comp hms.tendsto_atTop)
    (fun z : K × T => f (A z.2 z.1)) (f.continuous.comp (hA.comp continuous_swap))
    (t ∘ ns ∘ ms) t₀ ht
  have he : (∫ x, f (A t₀ x) ∂μ) = ∫ x, f x ∂μ := by
    calc
      _ = ∫ x, f x ∂Measure.map (A t₀) μ :=
        (integral_map (hm t₀).measurable.aemeasurable f.continuous.aestronglyMeasurable).symm
      _ = _ := by rw [(hm t₀).map_eq]
  simpa only [Function.comp_def, he] using h

end
end BapatRealExistence
