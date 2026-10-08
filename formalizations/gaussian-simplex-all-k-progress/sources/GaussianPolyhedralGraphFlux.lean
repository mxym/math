import GaussianSliceFlux
import GaussianWinningPartition

/-! Flux for a polyhedral epigraph, decomposed into its actual exposed graph
facets. All boundary terms are explicit Gaussian-density integrals. Identifying
them with intrinsic facet area is a separate, still necessary geometric step. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma standardDensity_le_zero (x : ℝ) : standardDensity x ≤ standardDensity 0 := by
  rw [standardDensity_eq, standardDensity_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg x]

lemma integrable_standardDensity_comp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) :
    Integrable (fun x => standardDensity (f x)) μ := by
  have hc : Continuous standardDensity := continuous_iff_continuousAt.mpr
    (fun x => (standardDensity_hasDerivAt x).continuousAt)
  apply (integrable_const (standardDensity 0)).mono'
    (hc.measurable.comp hf).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_pos (standardDensity_pos _)]
    exact standardDensity_le_zero _

/-- Graph facets selected by the strict maximum partition the polyhedral
epigraph flux. Pairwise-distinct graph slopes make all ambiguous edges null. -/
theorem gaussian_polyhedral_graph_flux (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    (∫ z in {z : Space d × ℝ | scoreMax v b z.1 < z.2},
      z.2 ∂(gaussian d).prod (gaussianReal 0 1)) =
      ∑ i, ∫ y in winningCell v b i, standardDensity (⟪v i, y⟫ - b i) ∂gaussian d := by
  rw [gaussian_epigraph_coordinate_flux _ _ (continuous_scoreMax v b).measurable]
  have he : (fun y : Space d => standardDensity (scoreMax v b y)) =ᵐ[gaussian d]
      (fun y => ∑ i, (winningCell v b i).indicator
        (fun y => standardDensity (⟪v i, y⟫ - b i)) y) := by
    filter_upwards [ae_unique_winner v b hv] with y hy
    obtain ⟨r, hr⟩ := hy
    rw [Finset.sum_eq_single r]
    · rw [Set.indicator_of_mem hr, scoreMax_eq_winning_score v b y r hr]
    · intro j _ hj
      have hn : y ∉ winningCell v b j := fun hjy =>
        (not_lt_of_gt (hr j hj)) (hjy r (Ne.symm hj))
      simp [hn]
    · simp
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator (measurableSet_winningCell v b i)
  · intro i _
    exact (integrable_standardDensity_comp (gaussian d) _ (by fun_prop)).indicator
      (measurableSet_winningCell v b i)

end GaussianMeasureBridge
