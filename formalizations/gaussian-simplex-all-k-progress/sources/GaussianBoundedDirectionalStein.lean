import GaussianBoundedCoordinateStein
import GaussianSmoothWinningGradient

/-! The bounded smooth Gaussian Stein identity in arbitrary directions,
and actual first-moment limits of the explicit winning-cell approximants. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

lemma bounded_smooth_directional_integrable (ρ : Space d → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (B : ℝ) (hB : ∀ x,‖fderiv ℝ ρ x‖ ≤ B)
    (u : Space d) : Integrable (fun x => fderiv ℝ ρ x u) (gaussian d) := by
  have hc := hρ.continuous_fderiv (by simp)
  apply (integrable_const (B*‖u‖)).mono' (hc.clm_apply continuous_const).aestronglyMeasurable
  exact ae_of_all _ fun x => ((fderiv ℝ ρ x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg u))

lemma bounded_scalar_inner_integrable (ρ : Space d → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1) (u : Space d) :
    Integrable (fun x => ⟪u,x⟫*ρ x) (gaussian d) := by
  have hc : Continuous (fun x : Space d => ⟪u,x⟫*ρ x) :=
    (innerSL ℝ u).continuous.mul hρ
  apply (integrable_gaussian_inner u).norm.mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [norm_mul,Real.norm_eq_abs (ρ x),abs_of_nonneg (hb x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb x).2

theorem gaussian_bounded_directional_stein
    (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1)
    (B : ℝ) (hB : ∀ x,‖fderiv ℝ ρ x‖ ≤ B) (u : Space d) :
    (∫ x,fderiv ℝ ρ x u ∂gaussian d) = ∫ x,⟪u,x⟫*ρ x ∂gaussian d := by
  classical
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hu : (∑ i : Fin d,u i • e i)=u := by
    simpa only [e,EuclideanSpace.basisFun_inner] using e.sum_repr' u
  have hD (x : Space d) : fderiv ℝ ρ x u = ∑ i : Fin d,u i*fderiv ℝ ρ x (e i) := by
    calc
      _ = fderiv ℝ ρ x (∑ i : Fin d,u i • e i) := congrArg (fderiv ℝ ρ x) hu.symm
      _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]
  have hinner (x : Space d) : ⟪u,x⟫=∑ i : Fin d,u i*x i := by
    calc
      _ = ⟪∑ i : Fin d,u i • e i,x⟫ := congrArg (fun z => ⟪z,x⟫) hu.symm
      _ = _ := by simp only [sum_inner,real_inner_smul_left,e,EuclideanSpace.basisFun_inner]
  have hi (i : Fin d) : Integrable (fun x : Space d => x i*ρ x) (gaussian d) := by
    simpa only [e,EuclideanSpace.basisFun_inner] using
      bounded_scalar_inner_integrable ρ hρ.continuous hb (e i)
  calc
    _ = ∑ i : Fin d,u i*(∫ x,fderiv ℝ ρ x (e i) ∂gaussian d) := by
      simp_rw [hD]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        (bounded_smooth_directional_integrable ρ hρ B hB (e i)).const_mul (u i))]
      simp only [integral_const_mul]
    _ = ∑ i : Fin d,u i*(∫ x,x i*ρ x ∂gaussian d) := by
      simp_rw [e,gaussian_bounded_coordinate_stein ρ hρ hb B hB]
    _ = _ := by
      have he : (fun x : Space d => ⟪u,x⟫*ρ x) =
          fun x => ∑ i : Fin d,u i*(x i*ρ x) := by
        funext x
        rw [hinner,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he,integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (u i))]
      simp only [integral_const_mul]

end GaussianMeasureBridge
