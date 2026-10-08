import BapatRealGaussianTensor

set_option autoImplicit false
open MeasureTheory Set

namespace BapatRealExistence
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_realGaussian_weight :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-‖x‖^2)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [Function.comp_def, real_gaussian_weight_prod]
  have he : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa only [neg_one_mul] using (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1))
  exact Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℝ)) (fun _ => he)

theorem abs_log_norm_le_coordinate (i : ι) (x : EuclideanSpace ℝ ι) (hx : x i ≠ 0) :
    |Real.log ‖x‖| ≤ ‖x‖^2 + |Real.log (|x i|)| := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hxpos : 0 < |x i| := abs_pos.mpr hx
  have hnpos : 0 < ‖x‖ := hxpos.trans_le hcoord
  have hlo := Real.log_le_log hxpos hcoord
  have hhi := Real.log_le_sub_one_of_pos hnpos
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (Real.log (|x i|)),sq_nonneg ‖x‖]
  · nlinarith [abs_nonneg (Real.log (|x i|)),sq_nonneg (‖x‖-(1/2:ℝ))]

theorem integrable_realGaussian_log_norm (i : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.log ‖x‖ * Real.exp (-‖x‖^2)) := by
  have hi : Integrable (fun x : EuclideanSpace ℝ ι =>
      |Real.log (|x i|)| * Real.exp (-‖x‖^2)) := by
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_realGaussian_coordinate_log i).abs
  apply (integrable_realGaussian_norm_sq.add hi).mono'
  · have hl := Real.measurable_log.comp measurable_norm (α := EuclideanSpace ℝ ι)
    have he : Continuous (fun x : EuclideanSpace ℝ ι => Real.exp (-‖x‖^2)) := by fun_prop
    exact (hl.mul he.measurable).aestronglyMeasurable
  · filter_upwards [real_euclidean_coordinate_ne_zero_ae i] with x hx
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    dsimp only [Pi.add_apply]
    have h := mul_le_mul_of_nonneg_right (abs_log_norm_le_coordinate i x hx)
      (Real.exp_pos (-‖x‖^2)).le
    nlinarith

/-- Squared modulus of the canonical complex linear form on real Gaussian vectors. -/
def canonicalQuadratic (t : ℝ) (x : RealSpace4) : ℝ :=
  t*(x 0)^2 + (1-t)*(x 1)^2

theorem canonicalQuadratic_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1)
    (x : RealSpace4) (hx : x 0 ≠ 0) :
    0 < canonicalQuadratic t x ∧ canonicalQuadratic t x ≤ ‖x‖^2 ∧
      Real.log t + 2*Real.log (|x 0|) ≤ Real.log (canonicalQuadratic t x) ∧
      Real.log (canonicalQuadratic t x) ≤ 2*Real.log ‖x‖ := by
  have hl : t*(x 0)^2 ≤ canonicalQuadratic t x := by
    unfold canonicalQuadratic
    have := mul_nonneg (sub_nonneg.mpr ht') (sq_nonneg (x 1))
    linarith
  have hpos := (mul_pos ht (sq_pos_of_ne_zero hx)).trans_le hl
  have hc (i : Fin 4) : (x i)^2 ≤ ‖x‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (x i)) (PiLp.norm_apply_le x i) 2
  have hupper : canonicalQuadratic t x ≤ ‖x‖^2 := by
    have h0 := mul_le_mul_of_nonneg_left (hc 0) ht.le
    have h1 := mul_le_mul_of_nonneg_left (hc 1) (sub_nonneg.mpr ht')
    unfold canonicalQuadratic
    nlinarith
  refine ⟨hpos,hupper,?_,?_⟩
  · have h := Real.log_le_log (mul_pos ht (sq_pos_of_ne_zero hx)) hl
    simpa only [Real.log_mul ht.ne' (pow_ne_zero 2 hx), Real.log_pow,
      Real.log_abs, Nat.cast_ofNat] using h
  · simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hpos hupper

/-- Includes the degenerate real endpoint t=1; no exceptional logarithm is assumed integrable. -/
theorem integrable_realGaussian_log_quadratic {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    Integrable (fun x : RealSpace4 => Real.log (canonicalQuadratic t x)*Real.exp (-‖x‖^2)) := by
  have hl : Integrable (fun x : RealSpace4 =>
      (Real.log t+2*Real.log (|x 0|))*Real.exp (-‖x‖^2)) := by
    convert (integrable_realGaussian_weight (ι := Fin 4)).const_mul (Real.log t) |>.add
      ((integrable_realGaussian_coordinate_log (0:Fin 4)).const_mul 2) using 1
    ext x
    dsimp only [Pi.add_apply]
    ring
  have hu : Integrable (fun x : RealSpace4 => 2*Real.log ‖x‖ * Real.exp (-‖x‖^2)) := by
    convert (integrable_realGaussian_log_norm (0:Fin 4)).const_mul 2 using 1
    ext x
    ring
  refine integrable_of_le_of_le ?_ ?_ ?_ hl hu
  · have hq : Continuous (canonicalQuadratic t) := by unfold canonicalQuadratic; fun_prop
    have he : Continuous (fun x : RealSpace4 => Real.exp (-‖x‖^2)) := by fun_prop
    exact ((Real.measurable_log.comp hq.measurable).mul he.measurable).aestronglyMeasurable
  · filter_upwards [real_euclidean_coordinate_ne_zero_ae (0:Fin 4)] with x hx
    exact mul_le_mul_of_nonneg_right (canonicalQuadratic_bounds ht ht' x hx).2.2.1
      (Real.exp_pos _).le
  · filter_upwards [real_euclidean_coordinate_ne_zero_ae (0:Fin 4)] with x hx
    exact mul_le_mul_of_nonneg_right (canonicalQuadratic_bounds ht ht' x hx).2.2.2
      (Real.exp_pos _).le

end
end BapatRealExistence
