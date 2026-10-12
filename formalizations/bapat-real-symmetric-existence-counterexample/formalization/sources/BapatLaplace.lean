import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Tactic

set_option autoImplicit false
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology

namespace BapatRealExistence

variable {α : Type*} [TopologicalSpace α] [CompactSpace α]
  [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  [IsFiniteMeasure μ] [IsOpenPosMeasure μ]

/-- Powers concentrate continuous observables that have a common value at all
maximizers. Pushing the measure to the compact range of `(c,g)` turns the whole
maximum set into one point, so no uniqueness or Hessian hypothesis is needed. -/
theorem tendsto_weighted_integral_common_maximum (c g : α → ℝ)
    (hc : Continuous c) (hg : Continuous g) (hnc : ∀ x, 0 ≤ c x)
    (x₀ : α) (hpos : 0 < c x₀) (hmax : ∀ x, c x ≤ c x₀)
    (hcommon : ∀ x, c x = c x₀ → g x = g x₀) :
    Tendsto (fun n : ℕ => (∫ x, c x ^ n ∂μ)⁻¹ * ∫ x, c x ^ n * g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  let ψ : α → ℝ × ℝ := fun x => (c x, g x)
  let ν : Measure (ℝ × ℝ) := μ.map ψ
  have hψ : Continuous ψ := hc.prodMk hg
  have hs : IsCompact (range ψ) := isCompact_range hψ
  have hν : ν.restrict (range ψ) = ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff hψ.measurable.aemeasurable hs.measurableSet).mpr
      (Eventually.of_forall (fun x => mem_range_self x))
  have hm : ∀ u : Set (ℝ × ℝ), IsOpen u → ψ x₀ ∈ u → 0 < ν (u ∩ range ψ) := by
    intro u hu hxu
    rw [Measure.map_apply hψ.measurable (hu.measurableSet.inter hs.measurableSet)]
    have he : ψ ⁻¹' (u ∩ range ψ) = ψ ⁻¹' u := by
      ext x
      simp
    rw [he]
    exact (hu.preimage hψ).measure_pos μ ⟨x₀, hxu⟩
  have hstrict : ∀ y ∈ range ψ, y ≠ ψ x₀ → y.1 < (ψ x₀).1 := by
    rintro y ⟨x, rfl⟩ hne
    apply lt_of_le_of_ne (hmax x)
    intro he
    exact hne (Prod.ext he (hcommon x he))
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
    (μ := ν) (g := fun y : ℝ × ℝ => y.2) hs hm continuous_fst.continuousOn hstrict
    (by rintro y ⟨x, rfl⟩; exact hnc x) hpos (mem_range_self x₀)
    (continuous_snd.continuousOn.integrableOn_compact hs) continuous_snd.continuousWithinAt
  have hd (n : ℕ) : (∫ y in range ψ, y.1 ^ n ∂ν) = ∫ x, c x ^ n ∂μ := by
    rw [hν]
    exact integral_map hψ.measurable.aemeasurable (continuous_fst.pow n).aestronglyMeasurable
  have hn (n : ℕ) : (∫ y in range ψ, y.1 ^ n * y.2 ∂ν) =
      ∫ x, c x ^ n * g x ∂μ := by
    rw [hν]
    exact integral_map hψ.measurable.aemeasurable
      ((continuous_fst.pow n).mul continuous_snd).aestronglyMeasurable
  simpa only [smul_eq_mul, hd, hn] using h

/-- The original numerator is used everywhere, including zeros of `c`.
No continuity, boundedness or integrability of the quotient `g/c` is assumed. -/
theorem tendsto_power_integral_ratio_common_maximum (c g : α → ℝ)
    (hc : Continuous c) (hg : Continuous g) (hnc : ∀ x, 0 ≤ c x)
    (x₀ : α) (hpos : 0 < c x₀) (hmax : ∀ x, c x ≤ c x₀)
    (hcommon : ∀ x, c x = c x₀ → g x = g x₀) :
    Tendsto (fun n : ℕ => (∫ x, c x ^ n * g x ∂μ) / ∫ x, c x ^ (n+1) ∂μ)
      atTop (𝓝 (g x₀ / c x₀)) := by
  have hG := tendsto_weighted_integral_common_maximum (μ := μ)
    c g hc hg hnc x₀ hpos hmax hcommon
  have hC : Tendsto (fun n : ℕ => (∫ x, c x ^ n ∂μ)⁻¹ * ∫ x, c x ^ (n+1) ∂μ)
      atTop (𝓝 (c x₀)) := by
    simpa only [pow_succ] using tendsto_weighted_integral_common_maximum (μ := μ)
      c c hc hc hnc x₀ hpos hmax (fun _ h => h)
  apply (hG.div hC hpos.ne').congr'
  filter_upwards [(tendsto_order.1 hC).1 0 hpos] with n hn
  have hD : (∫ x, c x ^ n ∂μ) ≠ 0 := by
    intro he
    simp [he] at hn
  exact mul_div_mul_left _ _ (inv_ne_zero hD)

/-- The exponent convention used in the real Gram construction. Here `f` will
be the modulus of the polynomial product and `g` the squared wedge norm.
Only their values at maximizers matter; the quotient is never used at zeros. -/
theorem tendsto_even_power_integral_ratio (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hnf : ∀ x, 0 ≤ f x)
    (x₀ : α) (hpos : 0 < f x₀) (hmax : ∀ x, f x ≤ f x₀)
    (hcommon : ∀ x, f x = f x₀ → g x = g x₀) :
    Tendsto (fun L : ℕ => (∫ x, f x ^ (2*L-2) * g x ∂μ) /
      ∫ x, f x ^ (2*L) ∂μ) atTop (𝓝 (g x₀ / (f x₀)^2)) := by
  have hsmax : ∀ x, (f x)^2 ≤ (f x₀)^2 := by
    intro x
    exact pow_le_pow_left₀ (hnf x) (hmax x) 2
  have hscommon : ∀ x, (f x)^2 = (f x₀)^2 → g x = g x₀ := by
    intro x hx
    apply hcommon x
    nlinarith [hnf x]
  have h := (tendsto_power_integral_ratio_common_maximum (μ := μ)
    (fun x => (f x)^2) g (hf.pow 2) hg (fun x => sq_nonneg (f x))
    x₀ (pow_pos hpos 2) hsmax hscommon).comp (tendsto_sub_atTop_nat 1)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [Function.comp_apply, Nat.sub_add_cancel hL, ← pow_mul,
    Nat.mul_sub_left_distrib, Nat.mul_one]

end BapatRealExistence
