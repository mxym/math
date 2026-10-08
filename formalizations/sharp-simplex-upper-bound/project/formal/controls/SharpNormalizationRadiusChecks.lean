import Entry005.SharpNormalizationRadius

noncomputable section
open Metric
open scoped BigOperators
namespace Entry005

-- Arbitrary-weight identity includes zero sum, not merely affine combinations.
example (d : ℕ) (hd : 1 ≤ d) (a : Fin (d + 1) → ℝ) (ha : ∑ i, a i = 0) :
    ‖∑ i, a i • (regularSimplex d hd).points i‖ ^ 2 =
      (d : ℝ) * (d + 1) * (∑ i, a i ^ 2) := by
  rw [regularSimplex_weighted_norm_sq, ha]
  ring

example (d : ℕ) (hd : 1 ≤ d) :
    ‖∑ i : Fin (d + 1), (0 : ℝ) • (regularSimplex d hd).points i‖ ^ 2 = 0 := by simp

-- The simplex vertex is an actual true-coordinate boundary point.
example (d : ℕ) (hd : 1 ≤ d) (j : Fin (d + 1)) :
    (∑ i, (simplexCoord (regularSimplex d hd) i ((regularSimplex d hd).points j)) ^ 2) = 1 := by
  classical
  change (∑ i, ((simplexAffineBasis (regularSimplex d hd)).coord i
    ((simplexAffineBasis (regularSimplex d hd)) j)) ^ 2) = 1
  simp [AffineBasis.coord_apply, Finset.sum_ite_eq']

example (d : ℕ) (hd : 1 ≤ d) (j : Fin (d + 1)) :
    ‖(regularSimplex d hd).points j‖ ^ 2 = (d : ℝ)^2 := by rw [regularSimplex_vertex_norm]

-- The true-coordinate norm identity works at the centroid, with zero geometric norm.
example (d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) * ((d + 1) * (∑ i, (simplexCoord (regularSimplex d hd) i 0)^2) - 1) = 0 := by
  rw [← regularSimplex_norm_sq_coord d hd 0]
  simp

-- A sum-one premise cannot be silently omitted when replacing (sum a)^2 by 1.
example (d : ℕ) (hd : 1 ≤ d) :
    ¬∀ a : Fin (d + 1) → ℝ,
      ‖∑ i, a i • (regularSimplex d hd).points i‖ ^ 2 =
        (d : ℝ) * ((d + 1) * (∑ i, a i ^ 2) - 1) := by
  intro h
  have hzero := h (fun _ => 0)
  simp only [zero_smul, Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_sub, mul_neg, mul_one] at hzero
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

-- Dimensions one and two are included without silently requiring d≥3.
example (K : ConvexBody (Space 1))
    (hmax : maximumInscribed K (regularSimplex 1 (by decide)))
    (x : Space 1) (hx : x ∈ (K : Set (Space 1))) : ‖x‖^2 ≤ 3 := by
  have hs := maximumInscribed_regular_norm_sq (by decide : 1 ≤ 1) K hmax x hx
  norm_num at hs
  exact hs
example (K : ConvexBody (Space 2))
    (hmax : maximumInscribed K (regularSimplex 2 (by decide))) :
    (K : Set (Space 2)) ⊆ closedBall 0 4 := by
  have hb := maximumInscribed_regular_sharp_ball (by decide : 1 ≤ 2) K hmax
  have hsqrt : Real.sqrt (2 + 2 : ℝ) = 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 + 2 : ℝ)]
  simpa only [Nat.cast_ofNat, hsqrt, show (2 : ℝ) * 2 = 4 by norm_num] using hb

-- This derived radius is strictly smaller than the preserved published R0 in every d≥1.
example (d : ℕ) (hd : 1 ≤ d) : (d : ℝ) * Real.sqrt (d + 2) < R0 d := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d + 2 by positivity)
  have hr : Real.sqrt (d + 2) < (d : ℝ) + 1 := by
    nlinarith [Real.sqrt_nonneg (d + 2)]
  unfold R0
  exact mul_lt_mul_of_pos_left hr (by positivity)

private def oversizedBody (d : ℕ) : ConvexBody (Space d) where
  carrier := closedBall 0 ((d : ℝ) * (d + 2))
  convex' := convex_closedBall _ _
  isCompact' := isCompact_closedBall _ _
  nonempty' := ⟨0, by simp; positivity⟩

private theorem oversized_vertex_norm (d : ℕ) (hd : 1 ≤ d) :
    ‖(d + 2 : ℝ) • (regularSimplex d hd).points 0‖ = (d : ℝ) * (d + 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), regularSimplex_vertex_norm]
  ring

-- A genuine compact convex body contains the unit ball and the actual regular simplex,
-- but violates the new radius bound: true maximality is indispensable.
example (d : ℕ) (hd : 1 ≤ d) :
    closedBall (0 : Space d) 1 ⊆ (oversizedBody d : Set (Space d)) ∧
    simplexSet (regularSimplex d hd) ⊆ (oversizedBody d : Set (Space d)) ∧
    ¬maximumInscribed (oversizedBody d) (regularSimplex d hd) := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨?_, ?_, ?_⟩
  · change closedBall (0 : Space d) 1 ⊆ closedBall 0 ((d : ℝ) * (d + 2))
    apply closedBall_subset_closedBall
    nlinarith
  · apply convexHull_min ?_ (oversizedBody d).convex
    rintro x ⟨i, rfl⟩
    change (regularSimplex d hd).points i ∈ closedBall 0 ((d : ℝ) * (d + 2))
    rw [mem_closedBall, dist_zero_right, regularSimplex_vertex_norm]
    nlinarith
  · intro hmax
    let x := (d + 2 : ℝ) • (regularSimplex d hd).points 0
    have hx : x ∈ (oversizedBody d : Set (Space d)) := by
      change ‖x - 0‖ ≤ (d : ℝ) * (d + 2)
      rw [sub_zero, oversized_vertex_norm]
    have hs := maximumInscribed_regular_norm_sq hd (oversizedBody d) hmax x hx
    rw [oversized_vertex_norm] at hs
    have hp : 0 < (d : ℝ)^2 * (d + 2) * (d + 1) := by positivity
    nlinarith

-- Without the absolute-coordinate bounds, even an actual point has a larger norm square.
example (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : Space d, (d : ℝ)^2 * (d + 2) < ‖x‖^2 := by
  refine ⟨(d + 2 : ℝ) • (regularSimplex d hd).points 0, ?_⟩
  rw [oversized_vertex_norm]
  have hp : 0 < (d : ℝ)^2 * (d + 2) * (d + 1) := by positivity
  nlinarith

-- The existential wrapper restores the same original simplex and its literal excess.
example {d : ℕ} (hd : 1 ≤ d) (K : ConvexBody (Space d))
    (S : Affine.Simplex ℝ (Space d) d) (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      (affineBody f K : Set (Space d)) ⊆ closedBall 0 ((d : ℝ) * Real.sqrt (d + 2)) ∧
      excess (affineBody f K : Set (Space d)) (affineSimplex f S) = excess (K : Set (Space d)) S := by
  obtain ⟨f, _, _, _, _, _, hb, he⟩ := maximum_simplex_sharp_radius_normalization hd K S hmax
  exact ⟨f, hb, he⟩

end Entry005
