import BapatCanonicalCloud

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_abs_inner_integral (a b : E) (hb : ‖b‖=1) :
    (∫ x : E, |inner ℝ a x| *Real.exp (-‖x‖^2)) =
      ‖a‖ * ∫ x : E, |inner ℝ b x| *Real.exp (-‖x‖^2) := by
  let R := (Submodule.span ℝ {a-‖a‖ • b})ᗮ.reflection
  have hR : R a = ‖a‖ • b := Submodule.reflection_sub (by simp [norm_smul,hb])
  calc
    _ = ∫ x : E, ‖a‖ * (|inner ℝ b (R x)| *Real.exp (-‖R x‖^2)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [← R.inner_map_map a x,hR,real_inner_smul_left,abs_mul,abs_norm,R.norm_map]
      ring
    _ = ‖a‖ * ∫ x : E, |inner ℝ b (R x)| *Real.exp (-‖R x‖^2) := integral_const_mul _ _
    _ = _ := by
      rw [R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
        (fun x : E => |inner ℝ b x| *Real.exp (-‖x‖^2))]
end General

theorem real_abs_gaussian_integral : (∫ x : ℝ, |x| *Real.exp (-x^2)) = 1 := by
  have hr := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => r*Real.exp (-r^2))
  have hi := integral_rpow_mul_exp_neg_rpow (p := 2) (q := 1) (by norm_num) (by norm_num)
  norm_num only [Real.rpow_one,Real.rpow_two,show ((1:ℝ)+1)/2=1 by norm_num,Real.Gamma_one] at hi
  simpa [Real.norm_eq_abs,sq_abs,Module.finrank_self,Nat.sub_self,pow_zero,one_smul,
    Real.volume_real_ball (by norm_num : (0:ℝ)≤1),smul_eq_mul,hi] using hr

theorem realGaussian_coordinate_zero_integral (f : ℝ → ℝ) :
    (∫ x : RealSpace4, f (x 0)*Real.exp (-‖x‖^2)) =
      (∫ x : ℝ, f x*Real.exp (-x^2)) * (Real.sqrt Real.pi)^3 := by
  rw [← (PiLp.volume_preserving_toLp (Fin 4)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  let g : Fin 4 → ℝ → ℝ := fun i x => (if i=0 then f x else 1)*Real.exp (-x^2)
  have he : (fun x : Fin 4 → ℝ => f (x 0)*Real.exp (-‖WithLp.toLp 2 x‖^2)) =
      fun x => ∏ i, g i (x i) := by
    ext x
    simp only [real_gaussian_weight_prod,g,Finset.prod_mul_distrib]
    simp
  rw [he,integral_fintype_prod_volume_eq_prod]
  have hgauss : (∫ x : ℝ, Real.exp (-x^2)) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul,div_one] using integral_gaussian (1:ℝ)
  simp [g,Fin.prod_univ_succ,hgauss]
  <;> ring

theorem real_four_gaussian_abs_inner_integral (a : RealSpace4) :
    (∫ x : RealSpace4, |inner ℝ a x| *Real.exp (-‖x‖^2)) =
      ‖a‖ * Real.pi * Real.sqrt Real.pi := by
  rw [gaussian_abs_inner_integral a (EuclideanSpace.single (0:Fin 4) 1) (by simp)]
  simp only [EuclideanSpace.inner_single_left,starRingEnd_apply,star_trivial,one_mul]
  rw [realGaussian_coordinate_zero_integral,real_abs_gaussian_integral,one_mul]
  rw [pow_succ (Real.sqrt Real.pi) 2,Real.sq_sqrt Real.pi_pos.le]
  ring

theorem complex_inv_norm_gaussian_integral :
    (∫ z : ℂ, ‖z‖⁻¹ * Real.exp (-‖z‖^2)) = Real.pi*Real.sqrt Real.pi := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := -1) (by norm_num) (by norm_num)
  simpa only [Real.rpow_neg_one,Real.rpow_two,show 2*Real.pi/2=Real.pi by ring,
    show ((-1:ℝ)+2)/2=1/2 by norm_num,Real.Gamma_one_half_eq] using h

theorem complex_inv_norm_gaussian_integrable :
    Integrable (fun z : ℂ => ‖z‖⁻¹ * Real.exp (-‖z‖^2)) := by
  apply Integrable.of_integral_ne_zero
  rw [complex_inv_norm_gaussian_integral]
  positivity

theorem complex_norm_gaussian_integral :
    (∫ z : ℂ, ‖z‖ * Real.exp (-‖z‖^2)) = Real.pi*Real.sqrt Real.pi/2 := by
  have h := complex_radial_gaussian_integral 1
  rw [show (((1:ℕ):ℝ)+2)/2=(1/2:ℝ)+1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1/2:ℝ)≠0),Real.Gamma_one_half_eq] at h
  simp only [pow_one] at h
  rw [h]
  ring

end
end BapatRealExistence
