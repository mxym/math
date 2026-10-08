import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
Partial real-analysis lemma for the written Gaussian argument.
All regularity, differential inequality, and endpoint hypotheses are explicit.
No Gaussian statement or Gaussian endpoint is introduced as an axiom.
-/
open Set Filter Topology

namespace GaussianRadialComparison

/-- A nonincreasing function whose right-hand limit is zero is nonpositive. -/
theorem antitone_nonpos_of_right_limit (g : ℝ → ℝ)
    (hm : AntitoneOn g (Ioo 0 1))
    (hl : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0))
    {t : ℝ} (ht : t ∈ Ioo 0 1) : g t ≤ 0 := by
  apply ge_of_tendsto hl
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t :=
    (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hpos
  exact hm ⟨hpos, lt_trans hs ht.2⟩ ht (le_of_lt hs)

/-- The quotient h(t)/t is nonincreasing under t*h'(t) <= h(t). -/
theorem ratio_antitone (h hp : ℝ → ℝ)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hi : ∀ t ∈ Ioo 0 1, t * hp t ≤ h t) :
    AntitoneOn (fun t => h t / t) (Ioo 0 1) := by
  have hg : ∀ t ∈ Ioo 0 1,
      HasDerivAt (fun s => h s / s) ((t * hp t - h t) / t^2) t := by
    intro t ht
    simpa only [id_eq, mul_one, mul_comm] using
      (hd t ht).fun_div (hasDerivAt_id t) (ne_of_gt ht.1)
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) 1)
  · intro t ht
    exact (hg t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hg t (by simpa only [interior_Ioo] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hti : t ∈ Ioo 0 1 := by simpa only [interior_Ioo] using ht
    rw [(hg t hti).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hi t hti)) (sq_nonneg t)

/-- Endpoint-continuous version with an explicit quotient limit. -/
theorem radial_comparison_of_ratio_limit (h hp : ℝ → ℝ)
    (hzero : h 0 = 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hi : ∀ t ∈ Ioo 0 1, t * hp t ≤ h t)
    (hl : Tendsto (fun t => h t / t) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hend : ContinuousWithinAt h (Iio 1) 1) :
    ∀ t ∈ Icc 0 1, h t ≤ 0 := by
  have hi0 : ∀ t ∈ Ioo 0 1, h t ≤ 0 := by
    intro t ht
    have hh := antitone_nonpos_of_right_limit (fun s => h s / s)
      (ratio_antitone h hp hd hi) hl ht
    simpa only [zero_mul] using (div_le_iff₀ ht.1).mp hh
  have h1 : h 1 ≤ 0 := by
    apply le_of_tendsto hend
    have hpos : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs hlt
    exact hi0 s ⟨hs, hlt⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · simpa only [← heq, hzero] using (le_refl (0 : ℝ))
  · rcases eq_or_lt_of_le ht.2 with heq | hlt
    · simpa only [heq] using h1
    · exact hi0 t ⟨hpos, hlt⟩

/-- The derivative-zero initial condition supplies the quotient limit. -/
theorem radial_comparison (h hp : ℝ → ℝ)
    (hzero : h 0 = 0)
    (hdzero : HasDerivAt h 0 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hi : ∀ t ∈ Ioo 0 1, t * hp t ≤ h t)
    (hend : ContinuousWithinAt h (Iio 1) 1) :
    ∀ t ∈ Icc 0 1, h t ≤ 0 := by
  apply radial_comparison_of_ratio_limit h hp hzero hd hi
  · simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hdzero.tendsto_slope_zero_right
  · exact hend

#print axioms antitone_nonpos_of_right_limit
#print axioms ratio_antitone
#print axioms radial_comparison_of_ratio_limit
#print axioms radial_comparison
end GaussianRadialComparison
