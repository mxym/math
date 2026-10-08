import GaussianCovarianceRadialDifferential
import GaussianIntrinsicInnerPerimeter
import GaussianRadialDeficitIntegral

/-! A reduction with its remaining perimeter hypothesis explicitly visible.
This file does NOT assert the all-k Gaussian perimeter theorem. All analytic
and actual covariance steps following that hypothesis are proved here. -/
open MeasureTheory ProbabilityTheory Module Matrix Set Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

def EqualMassSimplicialPerimeterBound (d : ℕ) : Prop :=
  ∀ v : Fin (d+2) → Space (d+1), AffineIndependent ℝ v →
    (d+1:ℕ)*simplexConstant (d+2)^2/2 ≤
      ((∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)^2

noncomputable def covarianceRadialTrace
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (t : ℝ) : ℝ :=
  (d+1:ℕ)*(covarianceValue (covarianceSegment Q t)-
    2*t*deriv (fun s : ℝ => covarianceValue (covarianceSegment Q s)) t)

noncomputable def covarianceRadialDeficit
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (t : ℝ) : ℝ :=
  covarianceValue (covarianceSegment Q t)*covarianceRadialTrace Q t/(d+1:ℕ)-
    simplexConstant (d+2)^2

lemma actual_radial_trace (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (t a T : ℝ)
    (hd : HasDerivAt (fun s : ℝ => covarianceValue (covarianceSegment Q s)) a t)
    (hi : t*a=(covarianceValue (covarianceSegment Q t)-T/(d+1:ℕ))/2) :
    covarianceRadialTrace Q t = T := by
  have hn : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
  have he : covarianceValue (covarianceSegment Q t)-2*t*a = T/(d+1:ℕ) := by linarith
  rw [covarianceRadialTrace,hd.deriv,he,mul_div_cancel₀ _ hn]

theorem covarianceRadialDeficit_nonneg_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (t : ℝ) (ht : t ∈ Ioo 0 1) : 0 ≤ covarianceRadialDeficit Q t := by
  obtain ⟨r,w,hr,hg,hw,hp,hs,hf,hd,hi⟩ := actual_covarianceSegment_radial_differential Q hQ t ht
  have hraw (i : Fin (d+2)) : rawWinningMoment r (canonicalPrices r) i =
      ∑ j,w i j • (r i-r j) := hf i
  have hl := hper r hr
  rw [actual_simplicial_cluster_inner_perimeter r _ hr w hraw] at hl
  have hn (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases he : i=j
    · subst j; rw [hw i]
    · exact (hp i j he).le
  have hc : covarianceValue (covarianceSegment Q t) =
      (∑ i,∑ j,w i j*‖r i-r j‖^2)/2 := by
    rw [← hg,covarianceValue_scoreGram,← balancedMoment_value r hr.injective]
    exact symmetric_flux_energy _ _ w hs hf
  have hcs := actual_flux_cauchy r w hn
  rw [← hc] at hcs
  have hb := GaussianSimplexAlgebra.perimeter_to_trace (d+1:ℕ)
    (fluxPerimeter r w) (simplexConstant (d+2))
    (covarianceValue (covarianceSegment Q t)) (fluxTrace w) (by positivity) hl hcs
  rw [covarianceRadialDeficit,actual_radial_trace Q t _ _ hd hi]
  exact sub_nonneg.mpr hb

lemma covariance_squared_radial_data
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q) :
    let H := fun t : ℝ => covarianceValue (covarianceSegment Q t)^2-simplexConstant (d+2)^2
    H 0 = 0 ∧ HasDerivAt H 0 0 ∧
      (∀ t ∈ Ioo 0 1,HasDerivAt H (deriv H t) t) ∧
      (∀ t ∈ Ioo 0 1,t*deriv H t-H t = -covarianceRadialDeficit Q t) ∧
      ContinuousWithinAt H (Iio 1) 1 := by
  dsimp only
  let C : ℝ → ℝ := fun t => covarianceValue (covarianceSegment Q t)
  let H : ℝ → ℝ := fun t => C t^2-simplexConstant (d+2)^2
  have h0 : H 0 = 0 := by simp [H,C,covarianceSegment_zero,covarianceValue_regular]
  have hd0 : HasDerivAt H 0 0 := by
    simpa [H,C] using ((covarianceSegment_stationary Q hQ).pow 2).sub_const (simplexConstant (d+2)^2)
  have hd (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt C (deriv C t) t := by
    obtain ⟨r,w,hr,hg,hw,hp,hs,hf,hc,hi⟩ := actual_covarianceSegment_radial_differential Q hQ t ht
    exact hc.differentiableAt.hasDerivAt
  have hH (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt H (deriv H t) t :=
    (((hd t ht).pow 2).sub_const _).differentiableAt.hasDerivAt
  have he (t : ℝ) (ht : t ∈ Ioo 0 1) : t*deriv H t-H t = -covarianceRadialDeficit Q t := by
    have hh := (((hd t ht).pow 2).sub_const (simplexConstant (d+2)^2)).deriv
    change deriv H t = _ at hh
    rw [hh]
    dsimp [H,C,covarianceRadialDeficit,covarianceRadialTrace]
    have hn : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
    ring
  exact ⟨h0,hd0,hH,he,((covarianceSegment_value_endpoint_continuous Q hQ.1).pow 2).sub_const _⟩

theorem covariance_comparison_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q) :
    covarianceValue Q ≤ simplexConstant (d+2) ∧
      IntegrableOn (fun t => covarianceRadialDeficit Q t/t^2) (Ioo 0 1) ∧
      (∫ t in Ioo 0 1,covarianceRadialDeficit Q t/t^2) =
        simplexConstant (d+2)^2-covarianceValue Q^2 := by
  let H : ℝ → ℝ := fun t => covarianceValue (covarianceSegment Q t)^2-simplexConstant (d+2)^2
  obtain ⟨h0,hd0,hd,hi,hend⟩ := covariance_squared_radial_data Q hQ
  have hD := covarianceRadialDeficit_nonneg_of_perimeter hper Q hQ
  have hineq (t : ℝ) (ht : t ∈ Ioo 0 1) : t*deriv H t ≤ H t := by
    have hh := hi t ht
    linarith [hD t ht]
  have hb := GaussianRadialComparison.radial_comparison H (deriv H) h0 hd0 hd hineq hend
  have h1 := hb 1 (by norm_num : (1:ℝ) ∈ Icc 0 1)
  simp only [H,covarianceSegment_one] at h1
  have hc : covarianceValue Q ≤ simplexConstant (d+2) := by
    have hn := simplexConstant_nonneg (k := d+2)
    nlinarith
  have hint := GaussianRadialComparison.radial_deficit_integral H (deriv H)
    (covarianceRadialDeficit Q) h0 hd0 hd hi hD hend
  refine ⟨hc,hint.1,?_⟩
  simpa only [H,covarianceSegment_one,neg_sub] using hint.2

end GaussianMeasureBridge
