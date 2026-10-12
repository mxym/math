import GaussianCutoffTestField

/-! Actual Gaussian integration by parts for bounded smooth scalar functions
with bounded derivative, without compact support. The proof takes limits of
the proved identities for genuine compact cutoff test fields. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem gaussian_bounded_coordinate_stein
    (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1)
    (B : ℝ) (hB : ∀ x,‖fderiv ℝ ρ x‖ ≤ B) (i : Fin d) :
    (∫ x,fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∂gaussian d) =
      ∫ x,x i*ρ x ∂gaussian d := by
  obtain ⟨C,hC0,hC⟩ := scaledGaussianCutoff_uniform_gradient_bound (d := d)
  let e : Space d := EuclideanSpace.basisFun (Fin d) ℝ i
  have he : ‖e‖=1 := by simp [e]
  have hρnorm (x : Space d) : ‖ρ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]
    exact (hb x).2
  have hleftbound (N : ℕ) : ∀ᵐ x ∂gaussian d,
      ‖ρ x*gaussianDivergence (coordinateCutoffTest N i) x‖ ≤ C+‖x i‖ := ae_of_all _ fun x => by
    have hd : ‖fderiv ℝ (scaledGaussianCutoff d N) x e‖ ≤ C := by
      have hh := ((fderiv ℝ (scaledGaussianCutoff d N) x).le_opNorm e).trans
        (mul_le_mul_of_nonneg_right (hC N x) (norm_nonneg e))
      simpa only [he,mul_one] using hh
    have hβnorm : ‖scaledGaussianCutoff d N x‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (scaledGaussianCutoff_bounds N x).1]
      exact (scaledGaussianCutoff_bounds N x).2
    calc
      _ ≤ ‖gaussianDivergence (coordinateCutoffTest N i) x‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hρnorm x)
      _ ≤ ‖fderiv ℝ (scaledGaussianCutoff d N) x e‖+‖x i*scaledGaussianCutoff d N x‖ := by
        rw [coordinateCutoffTest_divergence]
        exact norm_sub_le _ _
      _ ≤ C+‖x i‖ := add_le_add hd (by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) hβnorm)
  have hleftpoint : ∀ᵐ x ∂gaussian d,
      Tendsto (fun N => ρ x*gaussianDivergence (coordinateCutoffTest N i) x) atTop
        (𝓝 (ρ x*(-x i))) := ae_of_all _ fun x => by
    have ht := (scaledGaussianCutoff_directional_tendsto_zero x e).sub
      ((tendsto_const_nhds (x := x i)).mul (scaledGaussianCutoff_tendsto x))
    have hh := (tendsto_const_nhds (x := ρ x)).mul ht
    simpa only [coordinateCutoffTest_divergence,mul_one,zero_sub] using hh
  have hL := tendsto_integral_of_dominated_convergence (fun x : Space d => C+‖x i‖)
    (fun N => (scalar_test_divergence_integrable ρ hρ (coordinateCutoffTest N i)).aestronglyMeasurable)
    ((integrable_const C).add (coordinate_gaussian_integrable i).norm) hleftbound hleftpoint
  have hrightbound (N : ℕ) : ∀ᵐ x ∂gaussian d,
      ‖fderiv ℝ ρ x (coordinateCutoffTest N i x)‖ ≤ B := ae_of_all _ fun x => by
    have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ ρ x)).trans (hB x)
    have hh := ((fderiv ℝ ρ x).le_opNorm (coordinateCutoffTest N i x)).trans
      (mul_le_mul (hB x) ((coordinateCutoffTest N i).norm_le x) (norm_nonneg _) hB0)
    simpa only [mul_one] using hh
  have hrightpoint : ∀ᵐ x ∂gaussian d,
      Tendsto (fun N => fderiv ℝ ρ x (coordinateCutoffTest N i x)) atTop
        (𝓝 (fderiv ℝ ρ x e)) := ae_of_all _ fun x => by
    have ht := (scaledGaussianCutoff_tendsto x).smul (tendsto_const_nhds (x := e))
    have ht' : Tendsto (fun N => coordinateCutoffTest N i x) atTop (𝓝 e) := by
      simpa only [coordinateCutoffTest,one_smul] using ht
    exact ((fderiv ℝ ρ x).continuous.tendsto e).comp ht'
  have hR := tendsto_integral_of_dominated_convergence (fun _ : Space d => B)
    (fun N => (scalar_test_directional_integrable ρ hρ (coordinateCutoffTest N i)).aestronglyMeasurable)
    (integrable_const B) hrightbound hrightpoint
  have hRn := hR.neg.congr' (Eventually.of_forall fun N =>
    (gaussian_smooth_test_integral ρ hρ hb (coordinateCutoffTest N i)).symm)
  have hh := tendsto_nhds_unique hL hRn
  have hi : (∫ x,ρ x*(-x i) ∂gaussian d) = -(∫ x,x i*ρ x ∂gaussian d) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  rw [hi] at hh
  change _=∫ x,x i*ρ x ∂gaussian d
  change _ = -(∫ x,fderiv ℝ ρ x e ∂gaussian d) at hh
  linarith

end GaussianMeasureBridge
