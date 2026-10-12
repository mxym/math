import Entry005.MaximumOuterBall
import Mathlib.Tactic.FinCases

noncomputable section
open Entry005 MeasureTheory Metric
open scoped BigOperators
namespace MaximumOuterBallChecks

private def point (r : ℝ) : Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => r)
private def segment (a b : ℝ) (h : a < b) : Affine.Simplex ℝ (Space 1) 1 :=
  ⟨![point a, point b], affineIndependent_of_ne ℝ (fun he => (ne_of_lt h)
    (congrArg (fun x : Space 1 => x 0) he))⟩

private def S := segment (-1) 1 (by norm_num)
private def L := segment (-2) 2 (by norm_num)

private def body (T : Affine.Simplex ℝ (Space 1) 1) : ConvexBody (Space 1) :=
  ⟨simplexSet T, convex_convexHull ℝ _, (Set.finite_range T.points).isCompact_convexHull ℝ,
    ⟨T.points 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩⟩

private theorem max_self (T : Affine.Simplex ℝ (Space 1) 1) : maximumInscribed (body T) T :=
  ⟨Set.Subset.refl _, fun _ ht => measure_mono ht⟩

private theorem norm_point (r : ℝ) : ‖point r‖ = |r| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  simp only [point, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

private theorem coord_formula (x : Space 1) :
    simplexCoord S 0 x = (1 - x 0) / 2 ∧ simplexCoord S 1 x = (1 + x 0) / 2 := by
  have hs := (simplexAffineBasis S).sum_coord_apply_eq_one x
  change (∑ i : Fin 2, simplexCoord S i x) = 1 at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change simplexCoord S 0 x + simplexCoord S 1 x = 1 at hs
  have hc := congrArg (fun y : Space 1 => y 0)
    ((simplexAffineBasis S).linear_combination_coord_eq_self x)
  change (∑ i : Fin 2, simplexCoord S i x • S.points i) 0 = x 0 at hc
  simp [Fin.sum_univ_succ, S, segment, point] at hc
  change -simplexCoord S 0 x + simplexCoord S 1 x = x 0 at hc
  constructor <;> linarith

-- Coordinate zero is an actual endpoint of the maximal simplex, with no division by it.
example : simplexCoord S 0 (point 1) = 0 := by
  have h := (coord_formula (point 1)).1
  norm_num [point] at h ⊢
  exact h

-- Actual maximality and both signed coordinate endpoints.
example : ∀ i : Fin 2, |simplexCoord S i (point (-1))| ≤ 1 := by
  have hx : point (-1) ∈ (body S : Set (Space 1)) := subset_convexHull ℝ _ ⟨0, rfl⟩
  exact fun i => maximumInscribed_coord_abs_le_one (le_refl 1) (body S) S
    (max_self S) (point (-1)) hx i

-- The literal published radius is obtained for an actual maximal norm-one segment.
example : (body S : Set (Space 1)) ⊆ closedBall 0 (R0 1) := by
  apply maximumInscribed_R0_ball (le_refl 1) (body S) S (max_self S)
  intro i
  fin_cases i <;> norm_num [S, segment, norm_point]

-- A negative coordinate produces an orientation-reversing genuine replacement,
-- with the same actual volume because its absolute determinant is one.
example : ∃ f : Space 1 ≃ᵃ[ℝ] Space 1,
    (∀ j, f (S.points j) = if j = 0 then point 3 else S.points j) ∧
    volume (simplexSet (affineSimplex f S)) = volume (simplexSet S) := by
  have hc : simplexCoord S 0 (point 3) = -1 := by
    have h := (coord_formula (point 3)).1
    norm_num [point] at h ⊢
    exact h
  obtain ⟨f, hf, hv⟩ := vertex_replacement_volume (le_refl 1) S 0 (point 3)
    (by rw [hc]; norm_num)
  refine ⟨f, hf, ?_⟩
  simpa [hc] using hv

-- The membership assumption matters even for a genuine maximal segment.
example : 1 < |simplexCoord S 1 (point 3)| := by
  rw [(coord_formula (point 3)).2]
  norm_num [point]

-- Without maximality the claim fails at a genuine point of a compact convex body.
example : ∃ x ∈ (body L : Set (Space 1)), 1 < |simplexCoord S 1 x| := by
  refine ⟨point 2, subset_convexHull ℝ _ ⟨1, rfl⟩, ?_⟩
  rw [(coord_formula (point 2)).2]
  norm_num [point]

end MaximumOuterBallChecks
