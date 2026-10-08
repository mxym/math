import BapatSpherePotential

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

def truncatedLogLinear (K : ℝ) (v : RealUnitSphere4) (z : ComplexUnitSphere4) : ℝ :=
  Real.log (max ‖realComplexLinear v z‖ (Real.exp (-K)))

@[fun_prop] theorem truncatedLogLinear_continuous (K : ℝ) :
    Continuous (fun p : RealUnitSphere4 × ComplexUnitSphere4 => truncatedLogLinear K p.1 p.2) := by
  apply Continuous.log
  · unfold realComplexLinear
    fun_prop
  · intro p
    exact (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne'

theorem log_le_truncatedLogLinear (K : ℝ) (v : RealUnitSphere4) (z : ComplexUnitSphere4)
    (hz : realComplexLinear v z ≠ 0) :
    Real.log ‖realComplexLinear v z‖ ≤ truncatedLogLinear K v z :=
  Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)

theorem abs_log_max_exp_le {x K : ℝ} (hx : 0<x) (hK : 0≤K) :
    |Real.log (max x (Real.exp (-K)))| ≤ |Real.log x| := by
  by_cases h : Real.exp (-K) ≤ x
  · rw [max_eq_left h]
  · have hxc : x < Real.exp (-K) := lt_of_not_ge h
    have hl : Real.log x ≤ -K := by
      simpa only [Real.log_exp] using Real.log_le_log hx hxc.le
    rw [max_eq_right hxc.le,Real.log_exp,abs_of_nonpos (by linarith : -K≤0),
      abs_of_nonpos (by linarith : Real.log x≤0)]
    linarith

theorem tendsto_log_max_exp_nat {x : ℝ} (hx : 0<x) :
    Tendsto (fun K : ℕ => Real.log (max x (Real.exp (-(K:ℝ))))) atTop (𝓝 (Real.log x)) := by
  have he : Tendsto (fun K : ℕ => Real.exp (-(K:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hcut := (tendsto_order.mp he).2 x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [hcut] with K hK
  rw [max_eq_left hK.le]

/-- The continuous truncations converge in integral to the actual finite logarithmic potential. -/
theorem truncatedPotential_integral_tendsto (z : ComplexUnitSphere4) :
    Tendsto (fun K : ℕ => ∫ v : RealUnitSphere4, truncatedLogLinear K v z
        ∂normalizedSphere (volume : Measure RealSpace4)) atTop (𝓝 (sphereLogPotential z)) := by
  apply tendsto_integral_of_dominated_convergence (fun v : RealUnitSphere4 =>
    |Real.log ‖realComplexLinear v z‖|)
  · intro K
    exact ((truncatedLogLinear_continuous K).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (realComplexLinear_log_integrable z).abs
  · intro K
    filter_upwards [realComplexLinear_ne_zero_ae z] with v hv
    exact abs_log_max_exp_le (norm_pos_iff.mpr hv) (Nat.cast_nonneg K)
  · filter_upwards [realComplexLinear_ne_zero_ae z] with v hv
    exact tendsto_log_max_exp_nat (norm_pos_iff.mpr hv)

/-- Moving maximizer representatives can be tested by every fixed continuous log truncation. -/
theorem truncatedPotential_empirical_moving (u : ℕ → RealUnitSphere4)
    (hu : ∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (z : ℕ → ComplexUnitSphere4)
    (z₀ : ComplexUnitSphere4) (hz : Tendsto z atTop (𝓝 z₀)) (K : ℝ) :
    Tendsto (fun n => empiricalAverage u (a n) (fun v => truncatedLogLinear K v (z n))) atTop
      (𝓝 (∫ v, truncatedLogLinear K v z₀ ∂normalizedSphere (volume : Measure RealSpace4))) :=
  tendsto_empirical_moving_parameter _ u hu a ha (fun p => truncatedLogLinear K p.1 p.2)
    (truncatedLogLinear_continuous K) z z₀ hz

end
end BapatRealExistence
