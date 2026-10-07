import Mxym

noncomputable section
open MeasureTheory Metric

namespace FinalIndependentAudit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- Definitional check that the set lives in the subspace and carries its volume.
example (U : Submodule ℝ E) (K : ConvexBody E) :
    Entry005.projectedVolume U K =
      volume (U.orthogonalProjectionOnto '' (K : Set E) : Set U) := rfl

-- The target functional and proved cap chain use exactly the same actual volume.
example (K : ConvexBody E) (u : E) :
    Entry005.projectionVolumeSet (K : Set E) u =
      (Entry005.projectedVolume (ℝ ∙ u)ᗮ K).toReal := rfl

-- Canonical Euclidean normalization, not an arbitrary Haar scaling parameter.
example (U : Submodule ℝ E) :
    volume (closedBall (0 : U) 1) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) 1) := by
  let b := stdOrthonormalBasis ℝ U
  have h := b.measurePreserving_repr.measure_preimage
    (s := closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) 1)
    measurableSet_closedBall.nullMeasurableSet
  have heq : b.repr ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) 1 =
      closedBall (0 : U) 1 := by
    ext x
    simp [mem_closedBall, dist_zero_right]
  rw [heq] at h
  exact h

-- No strict-positive eta assumption was silently inserted at the endpoint.
theorem zero_projection_deficit_forces_equality (hd : 2 ≤ Module.finrank ℝ E)
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
  have h := Entry005.hausdorff_from_projection_deficit hd K P M 0 hM (le_refl 0)
    hball hKP hPM hdef
  rw [Real.zero_rpow (one_div_ne_zero hm), mul_zero] at h
  have hz : Metric.hausdorffDist (K : Set E) (P : Set E) = 0 :=
    le_antisymm h Metric.hausdorffDist_nonneg
  exact (K.isClosed.hausdorffDist_zero_iff_eq P.isClosed
    (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty P.nonempty
      K.isCompact.isBounded P.isCompact.isBounded)).mp hz

#print axioms zero_projection_deficit_forces_equality
end FinalIndependentAudit
