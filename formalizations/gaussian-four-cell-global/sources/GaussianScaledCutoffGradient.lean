import GaussianScaledCutoff

/-! Uniform derivative control and vanishing directional derivatives of the
expanding smooth cutoffs, with all constants independent of the index. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma scaledGaussianCutoff_uniform_gradient_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ N (x : Space d),‖fderiv ℝ (scaledGaussianCutoff d N) x‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := fixedGaussianBump_derivative_bounded (d := d)
  refine ⟨C,hC0,fun N x => (scaledGaussianCutoff_derivative_bound C hC N x).trans ?_⟩
  apply (div_le_iff₀ (show 0 < (N : ℝ)+1 by positivity)).mpr
  nlinarith [mul_nonneg hC0 (Nat.cast_nonneg (α := ℝ) N)]

lemma scaledGaussianCutoff_directional_tendsto_zero (x u : Space d) :
    Tendsto (fun N => fderiv ℝ (scaledGaussianCutoff d N) x u) atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := fixedGaussianBump_derivative_bounded (d := d)
  have hR : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => C/((N : ℝ)+1)*‖u‖) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Pi.inv_apply,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := C)).mul hR.inv_tendsto_atTop).mul (tendsto_const_nhds (x := ‖u‖))
  apply squeeze_zero_norm (fun N => ?_) hlim
  exact ((fderiv ℝ (scaledGaussianCutoff d N) x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (scaledGaussianCutoff_derivative_bound C hC N x) (norm_nonneg u))

end GaussianMeasureBridge
