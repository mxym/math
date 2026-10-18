import Deviation.CompactFrequency

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def exponentialPrimitive (t u : ℝ) : ℂ :=
  ∫ z in (0:ℝ)..u,Complex.exp (((t*z:ℝ):ℂ)*Complex.I)

theorem exponentialPrimitive_norm_le (t u : ℝ) : ‖exponentialPrimitive t u‖≤|u| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=u) (C:=1)
    (f:=fun z : ℝ => Complex.exp (((t*z:ℝ):ℂ)*Complex.I))
    (fun z hz => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [exponentialPrimitive,one_mul,sub_zero] using h

theorem exponentialPrimitive_zero (u : ℝ) : exponentialPrimitive 0 u=(u:ℂ) := by
  simp [exponentialPrimitive]

theorem exponentialPrimitive_ne_zero (t u : ℝ) (ht : t≠0) :
    exponentialPrimitive t u=(Complex.exp (((t*u:ℝ):ℂ)*Complex.I)-1)/((t:ℂ)*Complex.I) := by
  have hc : (t:ℂ)*Complex.I≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have h := integral_exp_mul_complex (a:=(0:ℝ)) (b:=u) hc
  have heq : (fun z : ℝ => Complex.exp (((t*z:ℝ):ℂ)*Complex.I))=
      (fun z : ℝ => Complex.exp (((t:ℂ)*Complex.I)*(z:ℂ))) := by
    ext z
    congr 1
    push_cast
    ring
  rw [exponentialPrimitive,heq,h]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_mul]
  congr 2
  ring

def sincKernelPrimitive (u : ℝ) : ℝ := ∫ z in (0:ℝ)..u,sincKernel z

/-- The primitive's compact-frequency formula is derived by a justified
Bochner Fubini interchange over the actual compact frequency measure. -/
theorem sincKernelPrimitive_representation (u : ℝ) :
    (sincKernelPrimitive u:ℂ)=∫ t,exponentialPrimitive t u ∂compactFrequency := by
  letI : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) u)) :=
    ⟨by simp only [Measure.restrict_apply_univ,Real.volume_uIoc]; finiteness⟩
  have hint : Integrable (Function.uncurry (fun (z t : ℝ) =>
      Complex.exp (((t*z:ℝ):ℂ)*Complex.I)))
      ((volume.restrict (uIoc (0:ℝ) u)).prod compactFrequency) := by
    rw [← integrable_norm_iff (by fun_prop)]
    have heq : (fun a : ℝ×ℝ => ‖Function.uncurry (fun (z t : ℝ) =>
      Complex.exp (((t*z:ℝ):ℂ)*Complex.I)) a‖)=fun _ => (1:ℝ) := by
      ext ⟨z,t⟩
      exact Complex.norm_exp_ofReal_mul_I _
    rw [heq]
    exact integrable_const _
  have hcast : (sincKernelPrimitive u:ℂ)=∫ z in (0:ℝ)..u,(sincKernel z:ℂ) := by
    rw [sincKernelPrimitive]
    exact (intervalIntegral.integral_ofReal).symm
  rw [hcast]
  simp_rw [sincKernel_compact_representation]
  rw [intervalIntegral_integral_swap hint]
  rfl

end
end ExtractionDeviation
