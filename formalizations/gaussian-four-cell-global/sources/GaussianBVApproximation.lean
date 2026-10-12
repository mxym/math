import GaussianSmoothTestProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A sufficient analytic criterion for a Gaussian BV upper bound, proved
from actual smooth approximants. The criterion requires convergence of the
gradient integrals; it does not assume any perimeter conclusion. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma gaussian_smooth_test_upper (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1) (X : GaussianTestField d)
    (hi : Integrable (fun x => ‖fderiv ℝ ρ x‖) (gaussian d)) :
    (∫ x,ρ x*gaussianDivergence X x ∂gaussian d) ≤
      ∫ x,‖fderiv ℝ ρ x‖ ∂gaussian d := by
  rw [gaussian_smooth_test_integral ρ hρ hb X,← integral_neg]
  apply integral_mono_ae (scalar_test_directional_integrable ρ hρ X).neg hi
  exact ae_of_all _ fun x => by
    have hnorm := ((fderiv ℝ ρ x).le_opNorm (X x)).trans
      (mul_le_mul_of_nonneg_left (X.norm_le x) (norm_nonneg (fderiv ℝ ρ x)))
    have hh : |fderiv ℝ ρ x (X x)| ≤ ‖fderiv ℝ ρ x‖ := by
      simpa only [Real.norm_eq_abs,mul_one] using hnorm
    exact (neg_le_abs _).trans hh

theorem gaussianBV_upper_of_smooth_approximation
    (S : Set (Space d)) (hS : MeasurableSet S) (ρ : ℕ → Space d → ℝ) (P : ℝ)
    (hρ : ∀ n,ContDiff ℝ ∞ (ρ n))
    (hb : ∀ n x,0 ≤ ρ n x ∧ ρ n x ≤ 1)
    (hpoint : ∀ᵐ x ∂gaussian d,Tendsto (fun n => ρ n x) atTop (𝓝 (S.indicator (fun _ => (1 : ℝ)) x)))
    (hgrad : ∀ n,Integrable (fun x => ‖fderiv ℝ (ρ n) x‖) (gaussian d))
    (hgradlim : Tendsto (fun n => ∫ x,‖fderiv ℝ (ρ n) x‖ ∂gaussian d) atTop (𝓝 P)) :
    gaussianBVPerimeter S ≤ ENNReal.ofReal P := by
  apply iSup_le
  intro X
  have hl : Tendsto (fun n => ∫ x,ρ n x*gaussianDivergence X x ∂gaussian d) atTop
      (𝓝 (∫ x in S,gaussianDivergence X x ∂gaussian d)) := by
    have hm (n : ℕ) : AEStronglyMeasurable (fun x => ρ n x*gaussianDivergence X x) (gaussian d) :=
      ((hρ n).continuous.mul (gaussianDivergence_continuous X)).aestronglyMeasurable
    have hbound (n : ℕ) : ∀ᵐ x ∂gaussian d,
        ‖ρ n x*gaussianDivergence X x‖ ≤ ‖gaussianDivergence X x‖ := ae_of_all _ fun x => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hb n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb n x).2
    have hlim : ∀ᵐ x ∂gaussian d,Tendsto (fun n => ρ n x*gaussianDivergence X x) atTop
        (𝓝 (S.indicator (gaussianDivergence X) x)) := by
      filter_upwards [hpoint] with x hx
      have hh := hx.mul (tendsto_const_nhds (x := gaussianDivergence X x))
      convert hh using 1
      by_cases hs : x ∈ S <;> simp [hs]
    have hi := tendsto_integral_of_dominated_convergence
      (fun x => ‖gaussianDivergence X x‖) hm (gaussianDivergence_integrable X).norm hbound hlim
    simpa only [integral_indicator hS] using hi
  apply ENNReal.ofReal_le_ofReal
  exact le_of_tendsto_of_tendsto hl hgradlim
    (Eventually.of_forall fun n => gaussian_smooth_test_upper (ρ n) (hρ n) (hb n) X (hgrad n))

end GaussianMeasureBridge
