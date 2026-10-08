import GaussianBVBasicIdentities
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual indicator-L1 continuity of all compact Gaussian divergence tests,
and closure of Gaussian BV upper bounds under such convergence. This is a
lower-semicontinuity ingredient for the remaining minimization problem, not
a proof of compactness, existence of minimizers, or a sharp lower bound. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def gaussianIndicatorL1Distance (S T : Set (Space d)) : ℝ :=
  ∫ x,‖S.indicator (fun _ => (1 : ℝ)) x-T.indicator (fun _ => (1 : ℝ)) x‖ ∂gaussian d

lemma gaussianIndicatorL1_integrable (S T : Set (Space d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Integrable (fun x => ‖S.indicator (fun _ => (1 : ℝ)) x-
      T.indicator (fun _ => (1 : ℝ)) x‖) (gaussian d) :=
  ((integrable_const (1 : ℝ)).indicator hS).sub ((integrable_const (1 : ℝ)).indicator hT) |>.norm

lemma gaussian_test_indicatorL1_bound (X : GaussianTestField d) (C : ℝ)
    (hC : ∀ x,‖gaussianDivergence X x‖ ≤ C)
    (S T : Set (Space d)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ‖(∫ x in S,gaussianDivergence X x ∂gaussian d)-
      (∫ x in T,gaussianDivergence X x ∂gaussian d)‖ ≤ C*gaussianIndicatorL1Distance S T := by
  have hSi := (gaussianDivergence_integrable X).indicator hS
  have hTi := (gaussianDivergence_integrable X).indicator hT
  rw [← integral_indicator hS,← integral_indicator hT,← integral_sub hSi hTi]
  apply (norm_integral_le_integral_norm _).trans
  have he (x : Space d) : S.indicator (gaussianDivergence X) x-
      T.indicator (gaussianDivergence X) x =
      (S.indicator (fun _ => (1 : ℝ)) x-T.indicator (fun _ => (1 : ℝ)) x)*gaussianDivergence X x := by
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [hs,ht]
  calc
    _ ≤ ∫ x,C*‖S.indicator (fun _ => (1 : ℝ)) x-T.indicator (fun _ => (1 : ℝ)) x‖
        ∂gaussian d := by
      apply integral_mono_ae (hSi.sub hTi).norm ((gaussianIndicatorL1_integrable S T hS hT).const_mul C)
      exact ae_of_all _ fun x => by
        simp only [Pi.sub_apply]
        rw [he x,norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; rfl

theorem gaussian_test_integral_tendsto_of_indicatorL1
    (S : Set (Space d)) (T : ℕ → Set (Space d))
    (hS : MeasurableSet S) (hT : ∀ n,MeasurableSet (T n))
    (hdist : Tendsto (fun n => gaussianIndicatorL1Distance (T n) S) atTop (𝓝 0))
    (X : GaussianTestField d) :
    Tendsto (fun n => ∫ x in T n,gaussianDivergence X x ∂gaussian d) atTop
      (𝓝 (∫ x in S,gaussianDivergence X x ∂gaussian d)) := by
  obtain ⟨C,hC⟩ := (gaussianDivergence_hasCompactSupport X).exists_bound_of_continuous
    (gaussianDivergence_continuous X)
  have hzero : Tendsto (fun n => C*gaussianIndicatorL1Distance (T n) S) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hdist
  have hh := squeeze_zero_norm (fun n => gaussian_test_indicatorL1_bound X C hC (T n) S (hT n) hS) hzero
  have ht := hh.add_const (∫ x in S,gaussianDivergence X x ∂gaussian d)
  simpa only [sub_add_cancel,zero_add] using ht

theorem gaussianBV_upper_bound_closed_under_indicatorL1
    (S : Set (Space d)) (T : ℕ → Set (Space d)) (P : ℝ) (hP : 0 ≤ P)
    (hS : MeasurableSet S) (hT : ∀ n,MeasurableSet (T n))
    (hdist : Tendsto (fun n => gaussianIndicatorL1Distance (T n) S) atTop (𝓝 0))
    (hupper : ∀ n,gaussianBVPerimeter (T n) ≤ ENNReal.ofReal P) :
    gaussianBVPerimeter S ≤ ENNReal.ofReal P := by
  apply iSup_le
  intro X
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto_of_tendsto
    (gaussian_test_integral_tendsto_of_indicatorL1 S T hS hT hdist X) tendsto_const_nhds
  exact Eventually.of_forall fun n => (ENNReal.ofReal_le_ofReal_iff hP).mp
    ((gaussianBVPerimeter_ge_test (T n) X).trans (hupper n))

end GaussianMeasureBridge
