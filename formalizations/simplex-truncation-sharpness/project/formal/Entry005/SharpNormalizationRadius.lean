import Entry005.RegularSimplex
import Entry005.MaximumOuterBall

noncomputable section
open Metric
open scoped BigOperators
namespace Entry005

private theorem regular_gram (d : ℕ) (hd : 1 ≤ d) (i j : Fin (d + 1)) :
    inner ℝ ((regularSimplex d hd).points i) ((regularSimplex d hd).points j) =
      (d : ℝ) * (d + 1) * (if i = j then 1 else 0) - d := by
  classical
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, regularSimplex_vertex_norm]
    simp only [ite_true, mul_one]
    ring
  · rw [regularSimplex_vertex_inner d hd i j hij]
    simp [hij]

/-- The norm-square identity for arbitrary actual linear combinations of the constructed
regular vertices. No sum-one or norm identity is assumed. -/
theorem regularSimplex_weighted_norm_sq (d : ℕ) (hd : 1 ≤ d)
    (a : Fin (d + 1) → ℝ) :
    ‖∑ i, a i • (regularSimplex d hd).points i‖ ^ 2 =
      (d : ℝ) * ((d + 1) * (∑ i, (a i) ^ 2) - (∑ i, a i) ^ 2) := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [real_inner_smul_left, inner_sum, inner_smul_right, regular_gram]
  have hrow (i : Fin (d + 1)) :
      (∑ j, a j * ((d : ℝ) * (d + 1) * (if i = j then 1 else 0) - d)) =
      (d : ℝ) * (d + 1) * a i - d * (∑ j, a j) := by
    simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.sum_mul]
    ring
  simp_rw [hrow, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hdiag : (∑ i, a i * ((d : ℝ) * (d + 1) * a i)) =
      (d : ℝ) * (d + 1) * (∑ i, a i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag, ← Finset.sum_mul]
  ring

/-- The actual affine-basis barycentric coordinates give the exact geometric norm square. -/
theorem regularSimplex_norm_sq_coord (d : ℕ) (hd : 1 ≤ d) (x : Space d) :
    ‖x‖ ^ 2 = (d : ℝ) *
      ((d + 1) * (∑ i, (simplexCoord (regularSimplex d hd) i x) ^ 2) - 1) := by
  have hcomb : ∑ i, simplexCoord (regularSimplex d hd) i x •
      (regularSimplex d hd).points i = x :=
    (simplexAffineBasis (regularSimplex d hd)).linear_combination_coord_eq_self x
  have hsum : ∑ i, simplexCoord (regularSimplex d hd) i x = 1 :=
    (simplexAffineBasis (regularSimplex d hd)).sum_coord_apply_eq_one x
  have h := regularSimplex_weighted_norm_sq d hd
    (fun i => simplexCoord (regularSimplex d hd) i x)
  simpa only [hcomb, hsum, one_pow] using h

/-- Absolute true-coordinate bounds yield the stronger geometric norm-square bound. -/
theorem regularSimplex_norm_sq_le_of_coord_abs (d : ℕ) (hd : 1 ≤ d) (x : Space d)
    (hcoord : ∀ i, |simplexCoord (regularSimplex d hd) i x| ≤ 1) :
    ‖x‖ ^ 2 ≤ (d : ℝ) ^ 2 * (d + 2) := by
  have hsum : (∑ i, (simplexCoord (regularSimplex d hd) i x) ^ 2) ≤ (d : ℝ) + 1 := by
    calc
      (∑ i, (simplexCoord (regularSimplex d hd) i x) ^ 2) ≤
          ∑ _i : Fin (d + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hb := abs_le.mp (hcoord i)
        nlinarith
      _ = (d : ℝ) + 1 := by simp
  rw [regularSimplex_norm_sq_coord d hd x]
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hn0 : (0 : ℝ) ≤ d + 1 := by positivity
  calc
    (d : ℝ) * ((d + 1) * (∑ i, (simplexCoord (regularSimplex d hd) i x) ^ 2) - 1) ≤
        (d : ℝ) * ((d + 1) * (d + 1) - 1) := by gcongr
    _ = (d : ℝ) ^ 2 * (d + 2) := by ring

/-- Actual maximality supplies every true-coordinate bound, giving the body norm square. -/
theorem maximumInscribed_regular_norm_sq {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (hmax : maximumInscribed K (regularSimplex d hd))
    (x : Space d) (hx : x ∈ (K : Set (Space d))) :
    ‖x‖ ^ 2 ≤ (d : ℝ) ^ 2 * (d + 2) := by
  exact regularSimplex_norm_sq_le_of_coord_abs d hd x
    (fun i => maximumInscribed_coord_abs_le_one hd K (regularSimplex d hd) hmax x hx i)

/-- The actual normalized body lies in radius d*sqrt(d+2), derived from true maximality. -/
theorem maximumInscribed_regular_sharp_ball {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (hmax : maximumInscribed K (regularSimplex d hd)) :
    (K : Set (Space d)) ⊆ closedBall 0 ((d : ℝ) * Real.sqrt (d + 2)) := by
  intro x hx
  have hs := maximumInscribed_regular_norm_sq hd K hmax x hx
  have hr0 : 0 ≤ (d : ℝ) * Real.sqrt (d + 2) := by positivity
  have hr2 : ((d : ℝ) * Real.sqrt (d + 2)) ^ 2 = (d : ℝ) ^ 2 * (d + 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hb : ‖x‖ ≤ (d : ℝ) * Real.sqrt (d + 2) := by nlinarith [norm_nonneg x]
  simpa only [mem_closedBall, dist_zero_right] using hb

/-- Every prescribed genuine maximum simplex admits actual regular normalization with
the stronger body radius and exact restoration of its original-centroid excess. -/
theorem maximum_simplex_sharp_radius_normalization {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      affineSimplex f S = regularSimplex d hd ∧
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      (∀ i, ‖(affineSimplex f S).points i‖ = d) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      (affineBody f K : Set (Space d)) ⊆ closedBall 0 ((d : ℝ) * Real.sqrt (d + 2)) ∧
      excess (affineBody f K : Set (Space d)) (affineSimplex f S) =
        excess (K : Set (Space d)) S := by
  obtain ⟨f, he, hc, hb, hn, hm, hE⟩ := maximum_simplex_regular_normalization hd K S hmax
  have hr : (affineBody f K : Set (Space d)) ⊆ closedBall 0 ((d : ℝ) * Real.sqrt (d + 2)) := by
    apply maximumInscribed_regular_sharp_ball hd
    rwa [← he]
  exact ⟨f, he, hc, hb, hn, hm, hr, hE⟩

end Entry005
