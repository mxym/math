import Deviation.CDFConvolution

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

theorem exponentialPrimitive_eq_ite (t u : ℝ) :
    exponentialPrimitive t u=if t=0 then (u:ℂ) else
      (Complex.exp (((t*u:ℝ):ℂ)*Complex.I)-1)/((t:ℂ)*Complex.I) := by
  split_ifs with ht
  · rw [ht,exponentialPrimitive_zero]
  · exact exponentialPrimitive_ne_zero t u ht

theorem exponentialPrimitive_measurable :
    Measurable (fun p : ℝ×ℝ => exponentialPrimitive p.1 p.2) := by
  simp_rw [exponentialPrimitive_eq_ite]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · fun_prop
  · fun_prop

theorem exponentialPrimitive_product_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun z : ℝ => |z|) μ) (x : ℝ) :
    Integrable (fun p : ℝ×ℝ => exponentialPrimitive p.1 (x-p.2)) (compactFrequency.prod μ) := by
  have hmajor : Integrable (fun p : ℝ×ℝ => |x|+|p.2|) (compactFrequency.prod μ) :=
    (integrable_const _).add (habs.comp_snd compactFrequency)
  have hm : Measurable (fun p : ℝ×ℝ => exponentialPrimitive p.1 (x-p.2)) :=
    exponentialPrimitive_measurable.comp
      (show Measurable (fun p : ℝ×ℝ => (p.1,x-p.2)) by fun_prop)
  apply hmajor.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro p
  exact (exponentialPrimitive_norm_le _ _).trans (by simpa using abs_sub_le x 0 p.2)

theorem exponential_phase_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun z : ℝ => Complex.exp (((t*z:ℝ):ℂ)*Complex.I)) μ := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact ae_of_all _ (fun _ => (Complex.norm_exp_ofReal_mul_I _).le)

theorem exponentialPrimitive_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t x : ℝ) (ht : t≠0) :
    (∫ z,exponentialPrimitive t (x-z) ∂μ)=
      (Complex.exp (((t*x:ℝ):ℂ)*Complex.I)*charFun μ (-t)-1)/((t:ℂ)*Complex.I) := by
  simp_rw [exponentialPrimitive_ne_zero _ _ ht]
  have hex : (fun z : ℝ => Complex.exp (((t*(x-z):ℝ):ℂ)*Complex.I))=
      fun z : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I)*
        Complex.exp ((((-t)*z:ℝ):ℂ)*Complex.I) := by
    ext z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [integral_div]
  rw [integral_sub]
  · rw [hex,integral_const_mul,integral_const,probReal_univ,one_smul]
    have hcf : (∫ z,Complex.exp ((((-t)*z:ℝ):ℂ)*Complex.I) ∂μ)=charFun μ (-t) := by
      rw [charFun_apply_real]
      simp only [Complex.ofReal_mul]
    rw [hcf]
  · rw [hex]
    exact (exponential_phase_integrable μ (-t)).const_mul _
  · exact integrable_const _

theorem compactFrequency_ae_ne_zero : ∀ᵐ t ∂compactFrequency,t≠0 := by
  have h : compactFrequency {0}≤0 := by
    calc
      _ ≤ ((2:ℝ≥0∞)⁻¹ • volume) {0} := compactFrequency_le_volume _
      _ = 0 := by simp
  rw [ae_iff]
  simpa using le_antisymm h bot_le

/-- A justified expectation/Fourier interchange for every actual probability
law with finite absolute first moment. -/
theorem sincKernelPrimitive_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun z : ℝ => |z|) μ) (x : ℝ) :
    (∫ z,(sincKernelPrimitive (x-z):ℂ) ∂μ)=
      ∫ t,(Complex.exp (((t*x:ℝ):ℂ)*Complex.I)*charFun μ (-t)-1)/
        ((t:ℂ)*Complex.I) ∂compactFrequency := by
  simp_rw [sincKernelPrimitive_representation]
  have hi : Integrable (Function.uncurry (fun (z t : ℝ) => exponentialPrimitive t (x-z)))
      (μ.prod compactFrequency) := (exponentialPrimitive_product_integrable μ habs x).swap
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [compactFrequency_ae_ne_zero] with t ht
  exact exponentialPrimitive_expectation μ t x ht

end
end ExtractionDeviation
