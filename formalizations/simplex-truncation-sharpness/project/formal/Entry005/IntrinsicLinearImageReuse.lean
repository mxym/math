import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Exact narrow reuse of the main owner's intrinsic linear image source.
Original source SHA256:
ed62871e6bbc9f97bc8071611e66a3c365cd1d798236837b6a1f108046ae06d8.
Only section IntrinsicVolume is extracted; the three theorem bodies below
are unchanged. No ZonotopeDeterminant or main-chain theorem is imported.
-/

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005.IntrinsicLinearImageReuse

section IntrinsicVolume

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem isometry_volume_image (e : E ≃ₗᵢ[ℝ] F) (S : Set E) :
    volume (e '' S) = volume S := by
  rw [← e.measurePreserving.map_eq]
  let em : E ≃ᵐ F := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  change (volume.map em) (em '' S) = volume S
  rw [em.map_apply, Set.preimage_image_eq S em.injective]

theorem translation_volume_image (a : E) (S : Set E) :
    volume ((fun x => a + x) '' S) = volume S := by
  have heq : (fun x => a + x) '' S = (fun x => -a + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-a + x, hx, by simp⟩
  rw [heq]
  exact measure_preimage_add volume (-a) S

/-- Canonical Euclidean volume scaling between distinct equal-dimensional
spaces, through arbitrary orthonormal bases. It includes singular maps and all
sets; no geometric body-volume identity is an input. -/
theorem orthonormal_linear_image_volume {d : ℕ} (bE : OrthonormalBasis (Fin d) ℝ E)
    (bF : OrthonormalBasis (Fin d) ℝ F) (f : E →ₗ[ℝ] F) (S : Set E) :
    volume (f '' S) =
      ENNReal.ofReal |bF.toBasis.det (fun i => f (bE i))| * volume S := by
  let e : F ≃ₗᵢ[ℝ] E := bF.repr.trans bE.repr.symm
  let g : E →ₗ[ℝ] E := e.toLinearMap.comp f
  have hdet : LinearMap.det g = bF.toBasis.det (fun i => f (bE i)) := by
    rw [← g.det_toMatrix bE.toBasis, Basis.det_apply]
    congr 1
    ext i j
    simp [g, e, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
      bE.coe_toBasis_repr_apply, bF.coe_toBasis_repr_apply]
  have himage : g '' S = e '' (f '' S) := Set.image_comp e f S
  rw [← isometry_volume_image e (f '' S), ← himage,
    Measure.addHaar_image_linearMap volume g S, hdet]

end IntrinsicVolume

end Entry005.IntrinsicLinearImageReuse
