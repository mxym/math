import GaussianBVIndicatorContinuity

/-! Gaussian masses are Lipschitz in actual indicator-L1 distance. In
particular exact prescribed masses are preserved by indicator-L1 limits. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma gaussianIndicatorL1Distance_symm (S T : Set (Space d)) :
    gaussianIndicatorL1Distance S T = gaussianIndicatorL1Distance T S := by
  unfold gaussianIndicatorL1Distance
  apply integral_congr_ae
  exact ae_of_all _ fun x => norm_sub_rev _ _

lemma gaussianIndicatorL1Distance_nonneg (S T : Set (Space d)) :
    0 ≤ gaussianIndicatorL1Distance S T := integral_nonneg (fun _ => norm_nonneg _)

theorem gaussian_mass_indicatorL1_bound (S T : Set (Space d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ‖(gaussian d).real S-(gaussian d).real T‖ ≤ gaussianIndicatorL1Distance S T := by
  have hSi := (integrable_const (1 : ℝ) (μ := gaussian d)).indicator hS
  have hTi := (integrable_const (1 : ℝ) (μ := gaussian d)).indicator hT
  rw [← integral_indicator_one hS,← integral_indicator_one hT]
  simp only [Pi.one_def]
  rw [← integral_sub hSi hTi]
  exact norm_integral_le_integral_norm _

theorem gaussian_mass_tendsto_of_indicatorL1
    (S : Set (Space d)) (T : ℕ → Set (Space d))
    (hS : MeasurableSet S) (hT : ∀ n,MeasurableSet (T n))
    (hdist : Tendsto (fun n => gaussianIndicatorL1Distance (T n) S) atTop (𝓝 0)) :
    Tendsto (fun n => (gaussian d).real (T n)) atTop (𝓝 ((gaussian d).real S)) := by
  have ht := squeeze_zero_norm (fun n => gaussian_mass_indicatorL1_bound (T n) S (hT n) hS) hdist
  have ha := ht.add_const ((gaussian d).real S)
  simpa only [sub_add_cancel,zero_add] using ha

theorem gaussian_fixed_mass_preserved_by_indicatorL1
    (S : Set (Space d)) (T : ℕ → Set (Space d)) (a : ℝ)
    (hS : MeasurableSet S) (hT : ∀ n,MeasurableSet (T n))
    (hdist : Tendsto (fun n => gaussianIndicatorL1Distance (T n) S) atTop (𝓝 0))
    (hmass : ∀ n,(gaussian d).real (T n)=a) : (gaussian d).real S=a := by
  have ht := gaussian_mass_tendsto_of_indicatorL1 S T hS hT hdist
  have hc : Tendsto (fun n => (gaussian d).real (T n)) atTop (𝓝 a) := by
    simpa only [hmass] using (tendsto_const_nhds (x := a) (f := atTop (α := ℕ)))
  exact tendsto_nhds_unique ht hc

end GaussianMeasureBridge
