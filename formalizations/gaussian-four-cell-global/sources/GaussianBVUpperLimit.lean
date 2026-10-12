import GaussianBVApproximation

/-! A Gaussian BV upper bound only needs an upper bounding sequence for
the gradient integrals. The gradient integrals need not converge themselves. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma gaussian_smooth_test_integral_tendsto
    (S : Set (Space d)) (hS : MeasurableSet S) (ρ : ℕ → Space d → ℝ)
    (hρ : ∀ n,ContDiff ℝ ∞ (ρ n)) (hb : ∀ n x,0 ≤ ρ n x ∧ ρ n x ≤ 1)
    (hpoint : ∀ᵐ x ∂gaussian d,Tendsto (fun n => ρ n x) atTop
      (𝓝 (S.indicator (fun _ => (1 : ℝ)) x))) (X : GaussianTestField d) :
    Tendsto (fun n => ∫ x,ρ n x*gaussianDivergence X x ∂gaussian d) atTop
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

theorem gaussianBV_upper_of_smooth_upper_limit
    (S : Set (Space d)) (hS : MeasurableSet S) (ρ : ℕ → Space d → ℝ)
    (G : ℕ → ℝ) (P : ℝ) (hρ : ∀ n,ContDiff ℝ ∞ (ρ n))
    (hb : ∀ n x,0 ≤ ρ n x ∧ ρ n x ≤ 1)
    (hpoint : ∀ᵐ x ∂gaussian d,Tendsto (fun n => ρ n x) atTop
      (𝓝 (S.indicator (fun _ => (1 : ℝ)) x)))
    (hgrad : ∀ n,Integrable (fun x => ‖fderiv ℝ (ρ n) x‖) (gaussian d))
    (hupper : ∀ n,(∫ x,‖fderiv ℝ (ρ n) x‖ ∂gaussian d) ≤ G n)
    (hG : Tendsto G atTop (𝓝 P)) :
    gaussianBVPerimeter S ≤ ENNReal.ofReal P := by
  apply iSup_le
  intro X
  have hl := gaussian_smooth_test_integral_tendsto S hS ρ hρ hb hpoint X
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto_of_tendsto hl hG
  exact Eventually.of_forall fun n =>
    (gaussian_smooth_test_upper (ρ n) (hρ n) (hb n) X (hgrad n)).trans (hupper n)

end GaussianMeasureBridge
