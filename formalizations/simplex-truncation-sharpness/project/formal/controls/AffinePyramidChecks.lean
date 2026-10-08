import Entry005.AffinePyramid

noncomputable section
open MeasureTheory
namespace Entry005.AffinePyramidChecks

private abbrev shiftThree : ℝ ≃ᵃ[ℝ] ℝ := AffineEquiv.vaddConst ℝ (3 : ℝ)

-- A translated base has the literal translated coordinate.
example : Entry005.liftedAffineEquiv shiftThree (WithLp.toLp 2 ((2 : ℝ), (0 : ℝ))) =
    WithLp.toLp 2 ((5 : ℝ), (0 : ℝ)) := by
  rw [Entry005.liftedAffineEquiv_base]
  norm_num [shiftThree, vadd_eq_add]

-- Its lift is a nontrivial shear at an intermediate height.
example : Entry005.liftedAffineEquiv shiftThree (WithLp.toLp 2 ((2 : ℝ), (1 / 2 : ℝ))) =
    WithLp.toLp 2 ((7 / 2 : ℝ), (1 / 2 : ℝ)) := by
  rw [Entry005.liftedAffineEquiv_apply]
  norm_num [shiftThree, vadd_eq_add]

-- The apex is fixed even when the base translation is nonzero.
example : Entry005.liftedAffineEquiv shiftThree (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) =
    WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) := by
  exact Entry005.liftedAffineEquiv_apex shiftThree

-- The inverse of the genuine equivalence recovers a sheared point.
example : (Entry005.liftedAffineEquiv shiftThree).symm
    (WithLp.toLp 2 ((7 / 2 : ℝ), (1 / 2 : ℝ))) =
    WithLp.toLp 2 ((2 : ℝ), (1 / 2 : ℝ)) := by
  apply (Entry005.liftedAffineEquiv shiftThree).injective
  rw [AffineEquiv.apply_symm_apply, Entry005.liftedAffineEquiv_apply]
  norm_num [shiftThree, vadd_eq_add]

-- A genuinely sheared two-dimensional base also lifts correctly.
example : Entry005.liftedAffineEquiv (Entry005.liftedAffineEquiv shiftThree)
    (WithLp.toLp 2 (WithLp.toLp 2 ((2 : ℝ), (1 / 2 : ℝ)), (0 : ℝ))) =
    WithLp.toLp 2 (WithLp.toLp 2 ((7 / 2 : ℝ), (1 / 2 : ℝ)), (0 : ℝ)) := by
  rw [Entry005.liftedAffineEquiv_base, Entry005.liftedAffineEquiv_apply]
  norm_num [shiftThree, vadd_eq_add]

-- Image equality uses the canonical hull on every base, including the empty set.
example : Entry005.pyramidSet (shiftThree '' (∅ : Set ℝ)) =
    Entry005.liftedAffineEquiv shiftThree '' Entry005.pyramidSet (∅ : Set ℝ) :=
  Entry005.pyramidSet_affine_image shiftThree ∅

-- A two-dimensional shear preserves actual Haar volume for an arbitrary set.
example (K : Set (WithLp 2 (ℝ × ℝ))) :
    volume (Entry005.liftedAffineEquiv shiftThree '' K) = volume K := by
  rw [Entry005.volume_affine_image_general, Entry005.liftedAffineEquiv_det]
  simp [shiftThree]

-- The new dimension is the actual module finrank.
example : Module.finrank ℝ (WithLp 2 ((WithLp 2 (ℝ × ℝ)) × ℝ)) = 3 := by
  rw [Entry005.finrank_lifted_space, Entry005.finrank_lifted_space]
  norm_num

end Entry005.AffinePyramidChecks
