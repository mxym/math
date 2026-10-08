import Entry005.ProjectionAffineTransport

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Entry005.ProjectionAffineTransportControls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- Exact all-set generic interface; no compactness, measurability of K, or volume
-- finiteness assumption is supplied.
example (L : E ≃ₗ[ℝ] E) (K : Set E) (u : E) (hu : u ≠ 0) :
    projectionVolumeSet (L '' K) u =
      (|LinearMap.det L.toLinearMap| * ‖L.symm u‖ / ‖u‖) *
        projectionVolumeSet K (L.symm u) :=
  projectionVolumeSet_linear_image L K u hu

-- The actual pyramid ambient space is accepted without a coordinate transfer.
example (L : WithLp 2 (E × ℝ) ≃ₗ[ℝ] WithLp 2 (E × ℝ))
    (K : Set (WithLp 2 (E × ℝ))) (u : WithLp 2 (E × ℝ)) (hu : u ≠ 0) :
    projectionVolumeSet (L '' K) u =
      (|LinearMap.det L.toLinearMap| * ‖L.symm u‖ / ‖u‖) *
        projectionVolumeSet K (L.symm u) :=
  projectionVolumeSet_linear_image L K u hu

example (L : E ≃ₗ[ℝ] E) (u : E) :
    projectionVolumeSet (L '' (∅ : Set E)) u = 0 := by
  simp [projectionVolumeSet]

example (K : Set E) (u : E) (hu : u ≠ 0) :
    projectionVolumeSet ((LinearEquiv.refl ℝ E) '' K) u = projectionVolumeSet K u := by
  simpa [hu] using projectionVolumeSet_linear_image (LinearEquiv.refl ℝ E) K u hu

private theorem volume_univ_of_subsingleton {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [Subsingleton F] : volume (Set.univ : Set F) = 1 := by
  let b := stdOrthonormalBasis ℝ F
  have hpp : parallelepiped b = (Set.univ : Set F) := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Subsingleton.elim x 0, mem_parallelepiped_iff]
    exact ⟨0, by simp, by simp⟩
  rw [← hpp]
  exact b.volume_parallelepiped

private theorem zero_dim_projection_volume :
    projectionVolumeSet (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) 0 = 1 := by
  have himage : (ℝ ∙ (0 : EuclideanSpace ℝ (Fin 0)))ᗮ.orthogonalProjectionOnto ''
      Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨(y : EuclideanSpace ℝ (Fin 0)), Set.mem_univ _, by simp⟩
  rw [projectionVolumeSet, himage, volume_univ_of_subsingleton]
  simp

-- The nonzero-normal boundary is necessary: the proposed formula at zero
-- already fails in dimension zero because canonical zero-dimensional volume is 1.
theorem zero_direction_counterexample :
    projectionVolumeSet
        ((LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))) '' Set.univ) 0 ≠
      (|LinearMap.det (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))).toLinearMap| *
        ‖(LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))).symm 0‖ / ‖(0 : EuclideanSpace ℝ (Fin 0))‖) *
      projectionVolumeSet (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))
        ((LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))).symm 0) := by
  simp [zero_dim_projection_volume]

-- The reused measure theorem includes singular maps, even though the exported
-- arbitrary-L transport theorem asks for a genuine linear equivalence.
example (S : Set ℝ) : volume ((0 : ℝ →ₗ[ℝ] ℝ) '' S) = 0 := by
  let b : OrthonormalBasis (Fin 1) ℝ ℝ :=
    (stdOrthonormalBasis ℝ ℝ).reindex (finCongr (by simp))
  have h := IntrinsicLinearImageReuse.orthonormal_linear_image_volume b b
    (0 : ℝ →ₗ[ℝ] ℝ) S
  simpa only [LinearMap.zero_apply, ← Pi.zero_def, AlternatingMap.map_zero,
    abs_zero, ENNReal.ofReal_zero, zero_mul] using h

#print axioms zero_direction_counterexample

end Entry005.ProjectionAffineTransportControls
