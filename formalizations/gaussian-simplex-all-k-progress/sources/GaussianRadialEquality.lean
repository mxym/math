import GaussianRadialDeficitIntegral

/-! Endpoint equality forces the radial deficit to vanish at every interior
point. This is a real-analysis rigidity theorem with explicit hypotheses. -/
open Set Filter MeasureTheory
open scoped Topology
namespace GaussianRadialComparison

lemma antitone_zero_of_two_endpoint_limits (g : ℝ → ℝ)
    (hm : AntitoneOn g (Ioo 0 1))
    (h0 : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 0))
    (h1 : Tendsto g (𝓝[<] (1:ℝ)) (𝓝 0)) :
    ∀ t ∈ Ioo 0 1, g t = 0 := by
  intro t ht
  have hl := antitone_nonpos_of_right_limit g hm h0 ht
  have hr : 0 ≤ g t := by
    apply le_of_tendsto h1
    have hnear : ∀ᶠ s in 𝓝[<] (1:ℝ), t < s :=
      (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear,self_mem_nhdsWithin] with s hs hlt
    exact hm ht ⟨lt_trans ht.1 hs,hlt⟩ hs.le
  exact le_antisymm hl hr

theorem radial_equality_forces_zero_deficit (h hp D : ℝ → ℝ)
    (hzero : h 0 = 0) (hdzero : HasDerivAt h 0 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hid : ∀ t ∈ Ioo 0 1, t * hp t - h t = -D t)
    (hD : ∀ t ∈ Ioo 0 1, 0 ≤ D t)
    (hend : ContinuousWithinAt h (Iio 1) 1) (he : h 1 = 0) :
    (∀ t ∈ Ioo 0 1, h t = 0) ∧ (∀ t ∈ Ioo 0 1, D t = 0) := by
  have hi (t : ℝ) (ht : t ∈ Ioo 0 1) : t*hp t ≤ h t := by
    linarith [hid t ht,hD t ht]
  have h0 : Tendsto (fun t => h t/t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hdzero.tendsto_slope_zero_right
  have h1 : Tendsto (fun t => h t/t) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have hh := hend.div continuousWithinAt_id (by norm_num : (1:ℝ) ≠ 0)
    change Tendsto (fun t => h t/t) (𝓝[<] (1:ℝ)) (𝓝 (h 1 / 1)) at hh
    simpa only [he,zero_div] using hh
  have hz (t : ℝ) (ht : t ∈ Ioo 0 1) : h t = 0 := by
    have hh := antitone_zero_of_two_endpoint_limits (fun t => h t/t)
      (ratio_antitone h hp hd hi) h0 h1 t ht
    exact (div_eq_zero_iff).mp hh |>.resolve_right ht.1.ne'
  refine ⟨hz,?_⟩
  intro t ht
  have hc : HasDerivAt h 0 t := by
    apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hz s hs
  have hh := (hd t ht).unique hc
  have hi := hid t ht
  rw [hh,hz t ht] at hi
  linarith

end GaussianRadialComparison
