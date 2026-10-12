import Entry005.EntryAffineInvariance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Entry005.AffineInvarianceControls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- Exact arbitrary-set interfaces, with no geometric identity supplied as an input.
example (hd : 1 ≤ Module.finrank ℝ E) (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    entryA (f '' K) = entryA K := entryA_affine_image hd f K

example (hd : 1 ≤ Module.finrank ℝ E) (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    entryDefect (f '' K) = entryDefect K := entryDefect_affine_image hd f K

example (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    projectionRatio (pyramidSet (f '' K)) = projectionRatio (pyramidSet K) :=
  projectionRatio_pyramid_affine_image f K

example (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    projectionBodySet (f '' K) =
      (|LinearMap.det f.linear.toLinearMap| • f.linear.symm.toLinearMap.adjoint) ''
        projectionBodySet K := projectionBodySet_affine_image f K

-- The all-normal characterization handles the zero normal itself.
example (K : Set E) (y : E) :
    inner ℝ (0 : E) y ≤ projectionBrightness K 0 := by
  simp [projectionBrightness]

example (K : Set E) (u : E) :
    projectionVolumeSet K (-u) = projectionVolumeSet K u := by
  simpa using projectionVolumeSet_smul_normal K u (-1) (by norm_num)

private abbrev translateThree : ℝ ≃ᵃ[ℝ] ℝ := AffineEquiv.vaddConst ℝ (3 : ℝ)

-- Dimension one is included, and actual empty sets have no hidden positivity premise.
example (K : Set ℝ) : entryA (translateThree '' K) = entryA K :=
  entryA_affine_image (by simp) translateThree K

example : entryDefect (translateThree '' (∅ : Set ℝ)) = entryDefect (∅ : Set ℝ) :=
  entryDefect_affine_image (by simp) translateThree ∅

-- A genuine two-dimensional shear, obtained from the proved translated-base lift.
-- It is not restricted to a similarity or an orthogonal change of coordinates.
private abbrev shear : WithLp 2 (ℝ × ℝ) ≃ᵃ[ℝ] WithLp 2 (ℝ × ℝ) :=
  liftedAffineEquiv translateThree

example (K : Set (WithLp 2 (ℝ × ℝ))) : entryA (shear '' K) = entryA K := by
  apply entryA_affine_image
  rw [finrank_lifted_space]
  simp

example (K : Set (WithLp 2 (ℝ × ℝ))) : entryDefect (shear '' K) = entryDefect K := by
  apply entryDefect_affine_image
  rw [finrank_lifted_space]
  simp

example : shear (WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ))) =
    WithLp.toLp 2 ((3 / 2 : ℝ), (1 / 2 : ℝ)) := by
  rw [liftedAffineEquiv_apply]
  norm_num [translateThree, vadd_eq_add]

-- The actual pyramid ambient dimension is accepted even for a zero-dimensional base.
example (f : EuclideanSpace ℝ (Fin 0) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 0))
    (K : Set (EuclideanSpace ℝ (Fin 0))) :
    projectionRatio (pyramidSet (f '' K)) = projectionRatio (pyramidSet K) :=
  projectionRatio_pyramid_affine_image f K

-- The wrapper preserves the original universally prescribed maximum simplex.
example {d : ℕ} (hd : 1 ≤ d) (f : Space d ≃ᵃ[ℝ] Space d)
    (K : ConvexBody (Space d)) :
    entryDefect (affineBody f K : Set (Space d)) = entryDefect (K : Set (Space d)) :=
  entryDefect_affineBody hd f K

end Entry005.AffineInvarianceControls
