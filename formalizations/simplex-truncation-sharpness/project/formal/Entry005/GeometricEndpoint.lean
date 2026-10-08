import Entry005.RegularSimplex
import Entry005.MaximumOuterBall

noncomputable section
open Metric
open scoped Pointwise
namespace Entry005

/-- The actual centered unit ball converts a genuine outer-radius bound to literal excess. -/
theorem excess_le_outer_radius_sub_one {d : ℕ} (A : Set (Space d))
    (S : Affine.Simplex ℝ (Space d) d) (R : ℝ) (hR : 1 ≤ R)
    (hc : S.centroid = 0) (hb : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hA : A ⊆ closedBall 0 R) : excess A S ≤ R - 1 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hcontain : A ⊆ R • simplexSet S := by
    intro x hx
    refine ⟨R⁻¹ • x, hb ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hRpos)]
      have hnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hA hx
      calc
        R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hRpos.le)
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    · change R • (R⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hRpos.ne', one_smul]
  unfold excess
  apply csInf_le
  · exact ⟨0, fun t ht => ht.1⟩
  · refine ⟨sub_nonneg.mpr hR, ?_⟩
    simpa only [centeredDilation, hc, sub_zero, zero_add, show 1 + (R - 1) = R by ring,
      Set.image_smul] using hcontain

/-- The global geometric bound holds for every prescribed genuine maximum simplex.
Normalization, maximum-coordinate bounds, and restoration of its original centroid are proved. -/
theorem maximum_simplex_excess_le_R0_sub_one {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) : excess (K : Set (Space d)) S ≤ R0 d - 1 := by
  obtain ⟨f, _, hc, hb, hn, hnormmax, he⟩ := maximum_simplex_regular_normalization hd K S hmax
  have houter := maximumInscribed_R0_ball hd (affineBody f K) (affineSimplex f S)
    hnormmax (fun i => (hn i).le)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 1 ≤ R0 d := by unfold R0; nlinarith
  rw [← he]
  exact excess_le_outer_radius_sub_one _ _ _ hR hc hb houter

/-- The complete geometric lane for every originally specified genuine maximum simplex.
The only local analytic input is the displayed actual intrinsic projection-deficit control
for an actual enclosing simplex, with its vertex bound and exact `d*rho ≤ 1/8` gate. -/
theorem maximum_simplex_regular_geometric_endpoint {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      (∀ i, ‖(affineSimplex f S).points i‖ = d) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      (affineBody f K : Set (Space d)) ⊆ closedBall 0 (R0 d) ∧
      excess (K : Set (Space d)) S ≤ R0 d - 1 ∧
      ∀ (P : Affine.Simplex ℝ (Space d) d) (M η : ℝ),
        (K : Set (Space d)) ⊆ simplexSet P →
        (∀ i, ‖(affineSimplex f P).points i‖ ≤ M) →
        0 ≤ η → (d : ℝ) * projectionHausdorffBound d M η ≤ 1 / 8 →
        (∀ u : Space d, ‖u‖ = 1 →
          (projectedVolume (ℝ ∙ u)ᗮ (simplexBody (affineSimplex f P))).toReal -
            (projectedVolume (ℝ ∙ u)ᗮ (affineBody f K)).toReal ≤ η) →
        excess (K : Set (Space d)) S ≤
          2 * M * (d : ℝ) * projectionHausdorffBound d M η := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨f, _, hc, hb, hn, hnormmax, _⟩ := maximum_simplex_regular_normalization hd1 K S hmax
  refine ⟨f, hc, hb, hn, hnormmax,
    maximumInscribed_R0_ball hd1 _ _ hnormmax (fun i => (hn i).le),
    maximum_simplex_excess_le_R0_sub_one hd1 K S hmax, ?_⟩
  intro P M η hKP hbound hη hgate hdef
  exact excess_of_projection_deficit_after_affine hd f K P S M η hmax hKP hc hb
    hbound hη hgate hdef

end Entry005
