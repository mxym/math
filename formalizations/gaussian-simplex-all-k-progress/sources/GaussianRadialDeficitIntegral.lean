import GaussianSimplexRadialComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact scalar deficit integral, including both singular endpoints.
All differential hypotheses remain explicit. Nonnegativity of the derivative
gives its integrability; no second derivative or smoothness is required. -/
open Set Filter MeasureTheory
open scoped Topology
namespace GaussianRadialComparison

lemma ratio_continuousOn_closed_interval (h hp : ℝ → ℝ)
    (hzero : h 0 = 0) (hdzero : HasDerivAt h 0 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hend : ContinuousWithinAt h (Iio 1) 1) :
    ContinuousOn (fun t => h t / t) (Icc 0 1) := by
  have hc0 : ContinuousAt (fun t => h t / t) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm,zero_mul] using
      hdzero.tendsto_slope_zero
  intro t ht
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with h0 | h1 | hi
  · rw [h0]
    exact hc0.continuousWithinAt
  · rw [h1]
    have he : ContinuousWithinAt (fun t => h t / t) (Iio 1) 1 :=
      hend.div continuousWithinAt_id (by norm_num)
    apply he.insert.mono
    intro x hx
    rcases eq_or_lt_of_le hx.2 with heq | hlt
    · exact Or.inl heq
    · exact Set.mem_insert_of_mem _ hlt
  · exact ((hd t hi).continuousAt.div continuousAt_id hi.1.ne').continuousWithinAt

/-- This is the improper deficit formula as a genuinely integrable function
on (0,1). It applies without regularity of the endpoint covariance. -/
theorem radial_deficit_integral (h hp D : ℝ → ℝ)
    (hzero : h 0 = 0) (hdzero : HasDerivAt h 0 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hid : ∀ t ∈ Ioo 0 1, t * hp t - h t = -D t)
    (hD : ∀ t ∈ Ioo 0 1, 0 ≤ D t)
    (hend : ContinuousWithinAt h (Iio 1) 1) :
    IntegrableOn (fun t => D t / t^2) (Ioo 0 1) ∧
      (∫ t in Ioo 0 1, D t / t^2) = -h 1 := by
  have hc := (ratio_continuousOn_closed_interval h hp hzero hdzero hd hend).neg
  have hg (t : ℝ) (ht : t ∈ Ioo 0 1) :
      HasDerivAt (fun s => -(h s/s)) (D t/t^2) t := by
    have hh := ((hd t ht).fun_div (hasDerivAt_id t) ht.1.ne').neg
    convert hh using 1
    · rfl
    · simp only [id_eq,mul_one,mul_comm]
      rw [hid t ht]
      ring
  have hn (t : ℝ) (ht : t ∈ Ioo 0 1) : 0 ≤ D t/t^2 :=
    div_nonneg (hD t ht) (sq_nonneg t)
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hc hg hn
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo).mp hi,?_⟩
  have hint : IntervalIntegrable (fun t => D t/t^2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) hc hg hint
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at he
  simpa using he

end GaussianRadialComparison
