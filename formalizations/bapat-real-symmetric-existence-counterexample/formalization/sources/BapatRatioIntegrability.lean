import BapatRatioRegroup

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

@[fun_prop] theorem balancedRealRatio_measurable : Measurable balancedRealRatio := by
  unfold balancedRealRatio
  fun_prop

theorem balancedRealRatio_sphere_integrable :
    Integrable (fun x : RealUnitSphere4 => |balancedRealRatio x|)
      (normalizedSphere (volume : Measure RealSpace4)) := by
  obtain ⟨y,hy⟩ := pairRatioGaussian_integrable.prod_left_ae.exists
  have hg : Integrable (fun x : RealSpace4 =>
      (|balancedRealRatio x-balancedRealRatio y| * Real.exp (-‖x‖^2))*Real.exp (-‖y‖^2)) := by
    apply hy.congr
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [pairRatioGaussian]
    ring
  have hg' : Integrable (fun x : RealSpace4 => |balancedRealRatio x-balancedRealRatio y| * Real.exp (-‖x‖^2)) :=
    (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (-‖y‖^2))) _).mp hg
  have hs := sphere_integrable_of_homogeneous_gaussian
    (fun x => |balancedRealRatio x-balancedRealRatio y|)
    (by intro r hr x; rw [balancedRealRatio_smul x r hr.ne']) hg'
  apply (hs.add (integrable_const |balancedRealRatio y|)).mono'
    (continuous_abs.measurable.comp (balancedRealRatio_measurable.comp measurable_subtype_coe)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Function.comp_def,Real.norm_eq_abs,abs_abs,Pi.add_apply]
  calc
    _ = |(balancedRealRatio x-balancedRealRatio y)+balancedRealRatio y| := by ring_nf
    _ ≤ _ := abs_add_le _ _

theorem balancedRealRatio_pair_sphere_integrable :
    Integrable (fun p : RealUnitSphere4 × RealUnitSphere4 =>
      |balancedRealRatio p.1-balancedRealRatio p.2|)
      ((normalizedSphere (volume : Measure RealSpace4)).prod
        (normalizedSphere (volume : Measure RealSpace4))) := by
  apply ((balancedRealRatio_sphere_integrable.comp_fst _).add
    (balancedRealRatio_sphere_integrable.comp_snd _)).mono'
    (by apply Measurable.aestronglyMeasurable; apply continuous_abs.measurable.comp; fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  simp only [Function.comp_def,Real.norm_eq_abs,abs_abs,Pi.add_apply]
  exact abs_sub _ _

theorem sphere_balancedRealRatio_prod_gini :
    (∫ p : RealUnitSphere4 × RealUnitSphere4, |balancedRealRatio p.1-balancedRealRatio p.2|
      ∂(normalizedSphere (volume : Measure RealSpace4)).prod
        (normalizedSphere (volume : Measure RealSpace4))) = Real.pi/2 := by
  rw [integral_prod _ balancedRealRatio_pair_sphere_integrable]
  exact sphere_balancedRealRatio_gini

end
end BapatRealExistence
