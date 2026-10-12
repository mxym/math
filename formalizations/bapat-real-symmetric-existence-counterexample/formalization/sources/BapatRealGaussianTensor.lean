import BapatGaussianLog

set_option autoImplicit false
open MeasureTheory Set

namespace BapatRealExistence
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_gaussian_weight_prod (x : EuclideanSpace ℝ ι) :
    Real.exp (-‖x‖^2) = ∏ i, Real.exp (-(x i)^2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, ← Finset.sum_neg_distrib, Real.exp_sum]

/-- Integrable one-coordinate tests extend to the actual isotropic Gaussian weight. -/
theorem integrable_realGaussian_coordinate (i : ι) (f : ℝ → ℝ)
    (hf : Integrable (fun x : ℝ => f x * Real.exp (-x^2))) :
    Integrable (fun x : EuclideanSpace ℝ ι => f (x i) * Real.exp (-‖x‖^2)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  let g : ι → ℝ → ℝ := fun j x => (if j=i then f x else 1)*Real.exp (-x^2)
  have hg (j : ι) : Integrable (g j) := by
    by_cases h : j=i
    · simpa only [g,if_pos h] using hf
    · simpa only [g,if_neg h,one_mul,neg_one_mul] using
        integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)
  have hp := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℝ)) hg
  convert hp using 1
  ext x
  simp only [Function.comp_def,real_gaussian_weight_prod,WithLp.ofLp_toLp,g,
    Finset.prod_mul_distrib]
  simp

theorem integrable_realGaussian_coordinate_log (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.log |x i| * Real.exp (-‖x‖^2)) :=
  integrable_realGaussian_coordinate i (fun x => Real.log |x|) integrable_log_abs_gaussian

theorem integrable_realGaussian_coordinate_sq (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => (x i)^2 * Real.exp (-‖x‖^2)) := by
  apply integrable_realGaussian_coordinate i (fun x => x^2)
  simpa only [Real.rpow_two,neg_one_mul] using
    integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1) (by norm_num : (-1:ℝ)<2)

theorem integrable_realGaussian_norm_sq :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^2 * Real.exp (-‖x‖^2)) := by
  have h := integrable_finset_sum Finset.univ (fun i _ => integrable_realGaussian_coordinate_sq (ι := ι) i)
  convert h using 1
  ext x
  simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,Finset.sum_mul]

/-- A coordinate vanishes only on a Lebesgue null hyperplane. -/
theorem real_euclidean_coordinate_ne_zero_ae (i : ι) :
    ∀ᵐ x : EuclideanSpace ℝ ι, x i ≠ 0 := by
  have h : ∀ᵐ x : ι → ℝ, x i ≠ 0 := Measure.ae_eval_ne (fun _ => volume) i 0
  exact (PiLp.volume_preserving_ofLp ι).quasiMeasurePreserving.ae h

end
end BapatRealExistence
