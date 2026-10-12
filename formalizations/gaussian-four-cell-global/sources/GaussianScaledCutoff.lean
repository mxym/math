import GaussianSmoothWinningGradient

/-! A fixed smooth bump rescaled to expanding balls. Its derivative bound
decays as the reciprocal radius; this supports Gaussian integration by parts
for bounded smooth functions without compact support. -/
open MeasureTheory ProbabilityTheory Module Set Metric Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def fixedGaussianBump (d : ℕ) : ContDiffBump (0 : Space d) :=
  ⟨1,2,by norm_num,by norm_num⟩

noncomputable def scaledGaussianCutoff (d N : ℕ) (x : Space d) : ℝ :=
  fixedGaussianBump d (((N : ℝ)+1)⁻¹ • x)

lemma scaledGaussianCutoff_contDiff (N : ℕ) : ContDiff ℝ ∞ (scaledGaussianCutoff d N) := by
  apply (fixedGaussianBump d).contDiff.comp
  fun_prop

lemma scaledGaussianCutoff_bounds (N : ℕ) (x : Space d) :
    0 ≤ scaledGaussianCutoff d N x ∧ scaledGaussianCutoff d N x ≤ 1 :=
  ⟨(fixedGaussianBump d).nonneg,(fixedGaussianBump d).le_one⟩

lemma scaledGaussianCutoff_compact (N : ℕ) : HasCompactSupport (scaledGaussianCutoff d N) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space d) (2*((N : ℝ)+1)))
  intro x hx
  have hR : 0 < (N : ℝ)+1 := by positivity
  have hh : ((N : ℝ)+1)⁻¹ • x ∈ Function.support (fixedGaussianBump d) := hx
  rw [(fixedGaussianBump d).support_eq] at hh
  have hn : ‖((N : ℝ)+1)⁻¹ • x‖=‖x‖/((N : ℝ)+1) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hR.le),div_eq_mul_inv,mul_comm]
  have hb : ‖x‖/((N : ℝ)+1)<2 := by simpa only [mem_ball_iff_norm,sub_zero,fixedGaussianBump,hn] using hh
  have hbn := (div_lt_iff₀ hR).mp hb
  simpa only [mem_closedBall,dist_zero_right] using hbn.le

lemma scaledGaussianCutoff_tendsto (x : Space d) :
    Tendsto (fun N => scaledGaussianCutoff d N x) atTop (𝓝 1) := by
  have hR : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hv := hR.inv_tendsto_atTop.smul (tendsto_const_nhds (x := x))
  have hv' : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹ • x) atTop (𝓝 (0 : Space d)) := by simpa using hv
  have he : fixedGaussianBump d (0 : Space d)=1 :=
    (fixedGaussianBump d).one_of_mem_closedBall (by simp [fixedGaussianBump])
  simpa only [scaledGaussianCutoff,Function.comp_def,he] using
    ((fixedGaussianBump d).continuous.tendsto (0 : Space d)).comp hv'

lemma fixedGaussianBump_derivative_bounded :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x : Space d,‖fderiv ℝ (fixedGaussianBump d) x‖ ≤ C := by
  have hsmooth : ContDiff ℝ ∞ (fixedGaussianBump d) := (fixedGaussianBump d).contDiff
  obtain ⟨C,hC⟩ := ((fixedGaussianBump d).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hsmooth.continuous_fderiv (by simp))
  exact ⟨C,(norm_nonneg _).trans (hC 0),hC⟩

lemma scaledGaussianCutoff_derivative_bound (C : ℝ)
    (hC : ∀ x : Space d,‖fderiv ℝ (fixedGaussianBump d) x‖ ≤ C) (N : ℕ) (x : Space d) :
    ‖fderiv ℝ (scaledGaussianCutoff d N) x‖ ≤ C/((N : ℝ)+1) := by
  have hR : 0 < (N : ℝ)+1 := by positivity
  have hs : HasFDerivAt (fun y : Space d => ((N : ℝ)+1)⁻¹ • y)
      (((N : ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ (Space d)) x := by
    convert (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (((N : ℝ)+1)⁻¹) using 1
    rfl
  have hsmooth : ContDiff ℝ ∞ (fixedGaussianBump d) := (fixedGaussianBump d).contDiff
  have hb : Differentiable ℝ (fixedGaussianBump d) := hsmooth.differentiable (by simp)
  have hd := (hb (((N : ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x hs
  have he : fderiv ℝ (scaledGaussianCutoff d N) x =
      (fderiv ℝ (fixedGaussianBump d) (((N : ℝ)+1)⁻¹ • x)).comp
        (((N : ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ (Space d)) := hd.fderiv
  rw [he]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hi : ‖((N : ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ (Space d)‖ ≤ ((N : ℝ)+1)⁻¹ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hR.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) ContinuousLinearMap.norm_id_le
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (fixedGaussianBump d) (0 : Space d))).trans (hC 0)
  calc
    _ ≤ C*((N : ℝ)+1)⁻¹ := mul_le_mul (hC _) hi (norm_nonneg _) hC0
    _ = _ := by rw [div_eq_mul_inv]

end GaussianMeasureBridge
