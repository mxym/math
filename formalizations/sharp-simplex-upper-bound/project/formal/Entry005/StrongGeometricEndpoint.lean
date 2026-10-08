import Entry005.StrongProjectionCap
import Entry005.SharpNormalizationRadius
import Entry005.CentroidMaximumBound
import Entry005.GeometricEndpoint

noncomputable section
open Metric
namespace Entry005

/-- Radius proved from genuine maximality and the actual regular Gram matrix. -/
def regularMaximumRadius (d : ℕ) : ℝ := (d : ℝ) * Real.sqrt ((d : ℝ) + 2)

/-- The non-circular cap's explicit Hausdorff radius. -/
def innerProjectionRadius (d : ℕ) (R η : ℝ) : ℝ :=
  2 * Real.sqrt ((d - 1 : ℕ) : ℝ) * (R + 1) * η ^ (1 / ((d - 1 : ℕ) : ℝ))

/-- An actual maximum supplies an admissible centered dilation, so literal excess is nonnegative. -/
theorem excess_nonnegative_of_maximum {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) : 0 ≤ excess (K : Set (Space d)) S := by
  unfold excess
  apply le_csInf
  · exact ⟨(d : ℝ) + 1, by positivity, maximumInscribed_centered_bound hd K S hmax⟩
  · intro t ht
    exact ht.1

/-- Improved actual projection-to-excess endpoint: the enclosing simplex has no assumed outer radius.
Its vertex bound is derived only after the true Hausdorff cap and smallness gate. -/
theorem excess_of_inner_radius_projection_deficit {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d) (R η : ℝ)
    (hmax : maximumInscribed K S) (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hc : S.centroid = 0) (hb : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hR : 0 ≤ R) (hKR : (K : Set (Space d)) ⊆ closedBall 0 R) (hη : 0 ≤ η)
    (hgate : (d : ℝ) * innerProjectionRadius d R η ≤ 1 / 8)
    (hdef : ∀ u : Space d, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ (simplexBody P)).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η) :
    excess (K : Set (Space d)) S ≤ 2 * (R + 1) * (d : ℝ) * innerProjectionRadius d R η := by
  let s := innerProjectionRadius d R η
  let β := Real.sqrt ((d - 1 : ℕ) : ℝ) * η ^ (1 / ((d - 1 : ℕ) : ℝ))
  have hs : 0 ≤ s := by dsimp [s, innerProjectionRadius]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsle : s ≤ 1 / 8 := by change (d : ℝ) * s ≤ 1 / 8 at hgate; nlinarith
  have hsβ : s = 2 * β * (R + 1) := by dsimp [s, β, innerProjectionRadius]; ring
  have hβR : 0 ≤ β * R := mul_nonneg hβ hR
  have hsmall : β ≤ 1 / 2 := by nlinarith
  have hdim : 2 ≤ Module.finrank ℝ (Space d) := by simpa [Space] using hd
  have hhaus := hausdorff_from_inner_radius_projection_deficit hdim K (simplexBody P) R η
    hR hη (fun x hx => hmax.1 (hb hx)) hKP hKR hdef
    (by simpa only [β, Space, finrank_euclideanSpace_fin] using hsmall)
  have hhaus' : hausdorffDist (K : Set (Space d)) (simplexSet P) ≤ s := by
    simp only [Space, finrank_euclideanSpace_fin] at hhaus
    exact hhaus
  have houter := outer_ball_after_small_hausdorff K (simplexBody P) R hKR (hhaus'.trans (by linarith))
  have hbound : ∀ i, ‖P.points i - S.centroid‖ ≤ R + 1 := by
    intro i
    rw [hc, sub_zero]
    have hp : P.points i ∈ simplexSet P := subset_convexHull ℝ _ ⟨i, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using houter hp
  exact excess_of_hausdorff_at_centroid (by omega) K P S (R + 1) s hmax hKP hbound
    (hc ▸ hb) hs hgate hhaus'

/-- Every originally prescribed actual maximum admits the sharper radius and global bound,
and the complete improved geometric local estimate with only actual projection data remaining. -/
theorem maximum_simplex_strong_geometric_endpoint {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      (∀ i, ‖(affineSimplex f S).points i‖ = d) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      (affineBody f K : Set (Space d)) ⊆ closedBall 0 (regularMaximumRadius d) ∧
      excess (K : Set (Space d)) S ≤ (d : ℝ) + 1 ∧
      ∀ (P : Affine.Simplex ℝ (Space d) d) (η : ℝ),
        (affineBody f K : Set (Space d)) ⊆ simplexSet P →
        0 ≤ η → (d : ℝ) * innerProjectionRadius d (regularMaximumRadius d) η ≤ 1 / 8 →
        (∀ u : Space d, ‖u‖ = 1 →
          (projectedVolume (ℝ ∙ u)ᗮ (simplexBody P)).toReal -
            (projectedVolume (ℝ ∙ u)ᗮ (affineBody f K)).toReal ≤ η) →
        excess (K : Set (Space d)) S ≤
          2 * (regularMaximumRadius d + 1) * (d : ℝ) *
            innerProjectionRadius d (regularMaximumRadius d) η := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨f, _, hc, hb, hn, hm, hr, hE⟩ := maximum_simplex_sharp_radius_normalization hd1 K S hmax
  refine ⟨f, hc, hb, hn, hm, hr, maximumInscribed_excess_le_dim_add_one hd1 K S hmax, ?_⟩
  intro P η hKP hη hgate hdef
  rw [← hE]
  exact excess_of_inner_radius_projection_deficit hd (affineBody f K) P (affineSimplex f S)
    (regularMaximumRadius d) η hm hKP hc hb (by unfold regularMaximumRadius; positivity)
    hr hη hgate hdef

/-- Zero actual projection deficit gives zero literal excess and equality of actual bodies. -/
theorem excess_eq_zero_of_zero_projection_deficit {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d) (R : ℝ)
    (hmax : maximumInscribed K S) (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hc : S.centroid = 0) (hb : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hR : 0 ≤ R) (hKR : (K : Set (Space d)) ⊆ closedBall 0 R)
    (hdef : ∀ u : Space d, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ (simplexBody P)).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ 0) :
    excess (K : Set (Space d)) S = 0 ∧ (K : Set (Space d)) = simplexSet P := by
  have hm : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hroot : (0 : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ)) = 0 := Real.zero_rpow (by positivity)
  have hs : innerProjectionRadius d R 0 = 0 := by simp only [innerProjectionRadius, hroot, mul_zero]
  have hE := excess_of_inner_radius_projection_deficit hd K P S R 0 hmax hKP hc hb hR hKR
    le_rfl (by rw [hs, mul_zero]; norm_num) hdef
  rw [hs, mul_zero] at hE
  have hdim : 2 ≤ Module.finrank ℝ (Space d) := by simpa [Space] using hd
  have heq := bodies_eq_of_zero_projection_deficit hdim K (simplexBody P) R hR
    (fun x hx => hmax.1 (hb hx)) hKP hKR hdef
  exact ⟨le_antisymm hE (excess_nonnegative_of_maximum (by omega) K S hmax),
    congrArg (fun C : ConvexBody (Space d) => (C : Set (Space d))) heq⟩

end Entry005
