import RadialComparison
-- Invalid weakening: h(t)=t, hp(t)=1 has h(0)=0 and t*hp(t)=h(t),
-- but its derivative at zero is 1 and its values on (0,1] are positive.
example (h hp : ℝ → ℝ) (hzero : h 0 = 0)
    (hd : ∀ t ∈ Set.Ioo 0 1, HasDerivAt h (hp t) t)
    (hi : ∀ t ∈ Set.Ioo 0 1, t * hp t ≤ h t)
    (hend : ContinuousWithinAt h (Set.Iio 1) 1) :
    ∀ t ∈ Set.Icc 0 1, h t ≤ 0 := by
  exact GaussianRadialComparison.radial_comparison h hp hzero (by assumption) hd hi hend
