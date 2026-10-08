import Entry005.ProjectionBodyCovariance
import Entry005.AffinePyramid
import Entry005.StrongGeometricEndpoint

noncomputable section
open Metric
namespace Entry005

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual pyramid ratio is invariant via the proved apex-fixing affine lift. -/
theorem projectionRatio_pyramid_affine_image (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    projectionRatio (pyramidSet (f '' K)) = projectionRatio (pyramidSet K) := by
  have hd : 1 ≤ Module.finrank ℝ (WithLp 2 (E × ℝ)) := by
    rw [finrank_lifted_space]
    omega
  rw [pyramidSet_affine_image, projectionRatio_affine_image hd]

/-- The exact canonical research invariant is affine invariant, proved from
actual projection-body covariance, actual Haar scaling and the actual pyramid lift. -/
theorem entryA_affine_image (hd : 1 ≤ Module.finrank ℝ E)
    (f : E ≃ᵃ[ℝ] E) (K : Set E) : entryA (f '' K) = entryA K := by
  unfold entryA
  rw [projectionRatio_pyramid_affine_image, projectionRatio_affine_image hd]

/-- Affine invariance of the exact canonical entry defect, without invariant-ratio premises. -/
theorem entryDefect_affine_image (hd : 1 ≤ Module.finrank ℝ E)
    (f : E ≃ᵃ[ℝ] E) (K : Set E) : entryDefect (f '' K) = entryDefect K := by
  unfold entryDefect
  rw [entryA_affine_image hd]

end General

/-- Actual body specialization in the exact Euclidean coordinates of the main target. -/
theorem entryA_affineBody {d : ℕ} (hd : 1 ≤ d) (f : Space d ≃ᵃ[ℝ] Space d)
    (K : ConvexBody (Space d)) : entryA (affineBody f K : Set (Space d)) = entryA (K : Set (Space d)) := by
  exact entryA_affine_image (by simpa [Space] using hd) f (K : Set (Space d))

/-- Original entry defect is exactly preserved by the actual normalized convex body. -/
theorem entryDefect_affineBody {d : ℕ} (hd : 1 ≤ d) (f : Space d ≃ᵃ[ℝ] Space d)
    (K : ConvexBody (Space d)) :
    entryDefect (affineBody f K : Set (Space d)) = entryDefect (K : Set (Space d)) := by
  exact entryDefect_affine_image (by simpa [Space] using hd) f (K : Set (Space d))

/-- Every originally prescribed maximum admits actual regular normalization,
the sharper proved outer radius, and exact preservation of BOTH research
invariant and original-centroid excess. -/
theorem maximum_simplex_strong_normalization_invariants {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      affineSimplex f S = regularSimplex d hd ∧
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      (affineBody f K : Set (Space d)) ⊆ closedBall 0 (regularMaximumRadius d) ∧
      entryA (affineBody f K : Set (Space d)) = entryA (K : Set (Space d)) ∧
      entryDefect (affineBody f K : Set (Space d)) = entryDefect (K : Set (Space d)) ∧
      excess (affineBody f K : Set (Space d)) (affineSimplex f S) = excess (K : Set (Space d)) S := by
  obtain ⟨f, he, hc, hb, _, hm, hr, hE⟩ := maximum_simplex_sharp_radius_normalization hd K S hmax
  exact ⟨f, he, hc, hb, hm, hr, entryA_affineBody hd f K, entryDefect_affineBody hd f K, hE⟩

end Entry005
