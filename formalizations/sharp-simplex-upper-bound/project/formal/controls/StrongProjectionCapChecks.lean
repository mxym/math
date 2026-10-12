import Entry005

noncomputable section

open Metric MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace StrongCapChecks

private def pointBody (x : ℝ) : ConvexBody ℝ where
  carrier := {x}
  convex' := convex_singleton x
  isCompact' := isCompact_singleton
  nonempty' := Set.singleton_nonempty x

/-- The metric intermediate radius is attained for two singleton bodies. -/
example : hausdorffDist (pointBody 0 : Set ℝ) (pointBody 2 : Set ℝ) = 2 := by
  change hausdorffDist ({0} : Set ℝ) {2} = 2
  rw [hausdorffDist_singleton]
  norm_num [Real.dist_eq]

/-- The derived intermediate radius uses the real Hausdorff distance. -/
example : (pointBody 2 : Set ℝ) ⊆ closedBall 0
    (0 + hausdorffDist (pointBody 0 : Set ℝ) (pointBody 2 : Set ℝ)) := by
  apply Entry005.body_outer_ball_from_hausdorff
  intro x hx
  change x ∈ ({0} : Set ℝ) at hx
  simpa only [Set.mem_singleton_iff.mp hx, mem_closedBall, dist_self] using le_refl (0 : ℝ)

/-- A small outer radius cannot be asserted before the distance is bounded. -/
example : ¬(pointBody 2 : Set ℝ) ⊆ closedBall 0 (0 + 1 : ℝ) := by
  intro h
  have htwo : (2 : ℝ) ∈ pointBody 2 := by change (2 : ℝ) ∈ ({2} : Set ℝ); simp
  have hdist := h htwo
  norm_num [mem_closedBall, Real.dist_eq] at hdist

/-- In target dimension one the cube fills the whole unit interval. -/
example : ENNReal.ofReal 2 ≤
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  simpa using Entry005.euclidean_unit_ball_sqrt_cube 1 (by omega)

/-- At target dimension four the new lower bound is one, rather than 1/16. -/
example : ENNReal.ofReal 1 ≤
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
  simpa only [Nat.cast_ofNat, hsqrt, div_self (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    using Entry005.euclidean_unit_ball_sqrt_cube 4 (by omega)

/-- The half-side 1/2 cube has a genuine unit-norm corner in dimension four. -/
example : ‖WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : ℝ))‖ = 1 := by
  have hsquare : ‖WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : ℝ))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : ℝ)))]

/-- The unscaled half-side-one cube is not contained in the unit ball. -/
example : WithLp.toLp 2 (fun _ : Fin 4 => (1 : ℝ)) ∉
    closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have hsquare : ‖WithLp.toLp 2 (fun _ : Fin 4 => (1 : ℝ))‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num
  intro h
  have hnorm : ‖WithLp.toLp 2 (fun _ : Fin 4 => (1 : ℝ))‖ ≤ 1 := by
    simpa [mem_closedBall, dist_zero_right] using h
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : Fin 4 => (1 : ℝ)))]

/-- The closed small-root gate includes β=1/2, in actual ambient dimension two. -/
example (K P : ConvexBody (EuclideanSpace ℝ (Fin 2))) (R : ℝ) (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ K) (hKP : K ≤ P)
    (hKR : (K : Set (EuclideanSpace ℝ (Fin 2))) ⊆ closedBall 0 R)
    (hdef : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 →
      (Entry005.projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (Entry005.projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ 1 / 2) :
    hausdorffDist (K : Set (EuclideanSpace ℝ (Fin 2))) P ≤ R + 1 := by
  have h := Entry005.hausdorff_from_inner_radius_projection_deficit
    (E := EuclideanSpace ℝ (Fin 2)) (by simp) K P R (1 / 2) hR (by norm_num)
    hball hKP hKR hdef (by norm_num)
  convert h using 1
  norm_num
  ring

/-- With zero deficit there is actual set equality, including the η=0 root case. -/
example (K P : ConvexBody (EuclideanSpace ℝ (Fin 2))) (R : ℝ) (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ K) (hKP : K ≤ P)
    (hKR : (K : Set (EuclideanSpace ℝ (Fin 2))) ⊆ closedBall 0 R)
    (hdef : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 →
      (Entry005.projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (Entry005.projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ 0) : K = P := by
  exact Entry005.bodies_eq_of_zero_projection_deficit (by simp) K P R hR
    hball hKP hKR hdef

end StrongCapChecks
