import Entry005

noncomputable section
open Metric MeasureTheory
namespace IndependentMeaningControls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The advertised zero-deficit endpoint really forces equality of actual bodies. -/
theorem zero_deficit_body_equality (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (hdef : ∀ u : E, ‖u‖ = 1 →
      (Entry005.projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (Entry005.projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ 0) :
    (K : Set E) = (P : Set E) := by
  have hm : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) ≠ 0 := by
    have hn : 0 < Module.finrank ℝ E - 1 := by omega
    exact_mod_cast hn.ne'
  have hroot : (0 : ℝ) ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) = 0 :=
    Real.zero_rpow (one_div_ne_zero hm)
  have hh := Entry005.hausdorff_from_projection_deficit hd K P M 0 hM (by rfl)
    hball hKP hPM hdef
  rw [hroot, mul_zero] at hh
  have heq : Metric.hausdorffDist (K : Set E) (P : Set E) = 0 :=
    le_antisymm hh Metric.hausdorffDist_nonneg
  exact (K.isClosed.hausdorffDist_zero_iff_eq P.isClosed
    (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty P.nonempty
      K.isCompact.isBounded P.isCompact.isBounded)).mp heq

#print axioms zero_deficit_body_equality

/-- The inner-ball hypothesis is inherited by every genuine projection. -/
example (U : Submodule ℝ E) (K : ConvexBody E)
    (hball : closedBall (0 : E) 1 ⊆ K) :
    closedBall (0 : U) 1 ⊆ Entry005.projectBody U K :=
  Entry005.project_body_unit_ball U K hball

/-- Unit directions truly produce hyperplanes of dimension d-1. -/
example (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 :=
  Entry005.hyperplane_dimension u hu

/-- The headline functional uses the same intrinsic projected-volume definition. -/
example (K : ConvexBody E) (u : E) :
    Entry005.projectionVolumeSet (K : Set E) u =
      (Entry005.projectedVolume (ℝ ∙ u)ᗮ K).toReal := rfl

end IndependentMeaningControls
