import RadialComparison

/-!
The nonzero-initial-derivative extension of the previously checked
one-dimensional radial comparison. All analytic hypotheses are explicit.
This is not a Gaussian-measure or multi-bubble formalization.
-/
open Set Filter Topology

namespace GaussianQuotaRadial

/-- Radial comparison with any prescribed initial derivative. -/
theorem tangent_radial_comparison (h hp : ℝ → ℝ) (ell : ℝ)
    (hzero : h 0 = 0)
    (hdzero : HasDerivAt h ell 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt h (hp t) t)
    (hi : ∀ t ∈ Ioo 0 1, t * hp t ≤ h t)
    (hend : ContinuousWithinAt h (Iio 1) 1) :
    ∀ t ∈ Icc 0 1, h t ≤ ell * t := by
  let g : ℝ → ℝ := fun t => h t - ell * t
  let gp : ℝ → ℝ := fun t => hp t - ell
  have hgzero : g 0 = 0 := by simp [g, hzero]
  have hgd0 : HasDerivAt g 0 0 := by
    simpa [g] using hdzero.fun_sub ((hasDerivAt_id (0 : ℝ)).const_mul ell)
  have hgd : ∀ t ∈ Ioo 0 1, HasDerivAt g (gp t) t := by
    intro t ht
    simpa [g, gp] using (hd t ht).fun_sub ((hasDerivAt_id t).const_mul ell)
  have hgi : ∀ t ∈ Ioo 0 1, t * gp t ≤ g t := by
    intro t ht
    have hh := hi t ht
    dsimp [gp, g]
    nlinarith
  have hge : ContinuousWithinAt g (Iio 1) 1 := by
    exact hend.sub (continuous_const.mul continuous_id).continuousWithinAt
  have hc := GaussianRadialComparison.radial_comparison
    g gp hgzero hgd0 hgd hgi hge
  intro t ht
  have hh := hc t ht
  dsimp [g] at hh
  linarith

#print axioms tangent_radial_comparison
end GaussianQuotaRadial
