import Entry005.PolarSimplexConstruction
import Entry005.ActualNormalizedDirectionalRoundness
import Entry005.SharpMainRetentionAssembly
import Entry005.ActualPyramidJointCone
import Entry005.EntryAffineInvariance

/-! Unconditional sharp upper stability for every prescribed maximum simplex.
The original target, constants, defect and centroid definitions are untouched.
The scale step uses actual radial facet cones, not finite Minkowski. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology
namespace Entry005

theorem normalized_sharp_upper_local {d : ℕ} [Nontrivial (Space d)] (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) (hcentroid : S.centroid = 0)
    (hbS : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (hsmall : entryDefect (K : Set (Space d)) ≤ eSharp d) :
    excess (K : Set (Space d)) S ≤ aSharp d *
      (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hb : closedBall (0 : Space d) 1 ⊆ K := hbS.trans hmax.1
  have he := actual_body_entryDefect_nonnegative (K : Set (Space d)) K.isCompact K.convex hb
  obtain ⟨μ, φ, hφ, hlim, _hraw, hball, hcenter, hbright,
      _hboundary, hsupport, _hhorizontal, _hA, _hentry, _hD, _hB,
      w, _hdet, hw, ha, hr, _hi, hcost⟩ :=
    actual_body_joint_polar_pyramid_assignment (K : Set (Space d)) K.isCompact K.convex hb
  have hbrightness : ∀ u : Space d, ‖u‖ = 1 →
      negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
        (fun x => dotProduct u x) = projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal) := by
    simpa only [Space, finrank_euclideanSpace_fin] using hbright
  let r := fun x => largestCoordinate (anchorCoordinates w x)
  have hround0 := normalized_convex_body_cone_directional_roundness hd K hb hbound
    (compactBallRawLaw μ : Measure (Fin d → ℝ)) hbrightness
  obtain ⟨_hQ, hround⟩ := same_witness_original_Q_and_round_hull hd1
    (compactBallRawLaw μ : Measure (Fin d → ℝ)) hball w (fun i => (hw i).2)
    r hr hround0 (entryDefect (K : Set (Space d))) he hsmall hcost
  obtain ⟨P, n, heights, _hhalfspaces, hKP, _hbP, hPM, hn, hh, hinj, hP, hatom, hsupp⟩ :=
    actual_polar_enclosing_simplex_original_radius hd K w ha (fun i => (hw i).2) hround
      (fun i => hsupport (hw i).1)
  have hcap := actual_finite_enclosing_body_strong_same_assignment_cap hd
    K (simplexBody P) hb hKP hbound hPM μ φ hφ hlim hcenter hbrightness
    n heights hn hh hinj hP w hatom (fun i => (hw i).2) ha hround hsupp
    r hr (entryDefect (K : Set (Space d))) he hsmall hcost
  exact normalized_maximum_simplex_excess_of_original_cap hd K P S hmax hKP hPM
    hcentroid hbS (entryDefect (K : Set (Space d))) he hsmall hcap

theorem sharpLocal : sharpLocalGoal := by
  intro d hd K _hK S hmax _he hsmall
  have hd1 : 1 ≤ d := by omega
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial (Space d) := inferInstance
  obtain ⟨f, _hregular, hcentroid, hbS, hnorm, hmaxf, hE⟩ :=
    maximum_simplex_regular_normalization hd1 K S hmax
  have hbound := maximumInscribed_R0_ball hd1 (affineBody f K) (affineSimplex f S)
    hmaxf (fun i => (hnorm i).le)
  have hdef := entryDefect_affineBody hd1 f K
  have hsmallf : entryDefect (affineBody f K : Set (Space d)) ≤ eSharp d := by
    rwa [hdef]
  have hlocal := normalized_sharp_upper_local (by omega) (affineBody f K)
    (affineSimplex f S) hmaxf hcentroid hbS hbound hsmallf
  rwa [hE, hdef] at hlocal

theorem actual_entryDefect_nonnegative_of_prescribed_maximum {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) : 0 ≤ entryDefect (K : Set (Space d)) := by
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial (Space d) := inferInstance
  obtain ⟨f, _hregular, _hcentroid, hbS, _hnorm, hmaxf, _hE⟩ :=
    maximum_simplex_regular_normalization hd K S hmax
  have hbK : closedBall (0 : Space d) 1 ⊆ affineBody f K := hbS.trans hmaxf.1
  have he := actual_body_entryDefect_nonnegative (affineBody f K : Set (Space d))
    (affineBody f K).isCompact (affineBody f K).convex hbK
  rwa [entryDefect_affineBody hd f K] at he

/-- The literal original unconditional Main target, with every maximum S. -/
theorem sharpMain : sharpMainGoal := by
  intro d hd K hK S hmax
  have hd1 : 1 ≤ d := by omega
  have he := actual_entryDefect_nonnegative_of_prescribed_maximum hd1 K S hmax
  exact original_global_scalar_gluing (by omega)
    (excess (K : Set (Space d)) S) (entryDefect (K : Set (Space d))) he
    (sharpLocal d hd K hK S hmax he)
    (maximum_simplex_excess_le_R0_sub_one hd1 K S hmax)

end Entry005
