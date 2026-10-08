import Entry005.CentroidMaximumBound
import Mathlib.Tactic.FinCases

noncomputable section
open Entry005 MeasureTheory
open scoped BigOperators
namespace CentroidMaximumBoundChecks

private def point (r : ℝ) : Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => r)
private def segment (a b : ℝ) (h : a < b) : Affine.Simplex ℝ (Space 1) 1 :=
  ⟨![point a, point b], affineIndependent_of_ne ℝ (fun he => (ne_of_lt h)
    (congrArg (fun x : Space 1 => x 0) he))⟩
private def S := segment 2 4 (by norm_num)
private def L := segment (-1) 7 (by norm_num)

private def body (T : Affine.Simplex ℝ (Space 1) 1) : ConvexBody (Space 1) :=
  ⟨simplexSet T, convex_convexHull ℝ _, (Set.finite_range T.points).isCompact_convexHull ℝ,
    ⟨T.points 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩⟩

private theorem max_self (T : Affine.Simplex ℝ (Space 1) 1) : maximumInscribed (body T) T :=
  ⟨Set.Subset.refl _, fun _ ht => measure_mono ht⟩

private theorem centroid_shifted : S.centroid = point 3 := by
  have h := S.centroid_vsub_eq (0 : Space 1)
  ext i
  fin_cases i
  have hh := congrArg (fun x : Space 1 => x 0) h
  norm_num [vsub_eq_sub, S, segment, point, Fin.sum_univ_succ] at hh ⊢
  exact hh

private theorem coord_formula (x : Space 1) :
    simplexCoord S 0 x = (4 - x 0) / 2 ∧ simplexCoord S 1 x = (x 0 - 2) / 2 := by
  have hs := (simplexAffineBasis S).sum_coord_apply_eq_one x
  change (∑ i : Fin 2, simplexCoord S i x) = 1 at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change simplexCoord S 0 x + simplexCoord S 1 x = 1 at hs
  have hc := congrArg (fun y : Space 1 => y 0)
    ((simplexAffineBasis S).linear_combination_coord_eq_self x)
  change (∑ i : Fin 2, simplexCoord S i x • S.points i) 0 = x 0 at hc
  simp [Fin.sum_univ_succ, S, segment, point] at hc
  change simplexCoord S 0 x * 2 + simplexCoord S 1 x * 4 = x 0 at hc
  constructor <;> linarith

-- The centroid is actually translated; no centroid-zero normalization is present.
example : S.centroid = point 3 := centroid_shifted
example : S.centroid ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space 1 => x 0) h
  rw [centroid_shifted] at he
  norm_num [point] at he

-- Uniform original-centroid coordinates for the translated genuine simplex.
example : ∀ i : Fin 2, simplexCoord S i (point 3) = 1 / 2 := by
  intro i
  have h := simplexCoord_centroid S i
  rw [centroid_shifted] at h
  norm_num at h
  exact h

-- The exact contraction factor is 1/3 and hits a simplex vertex at coordinate -1.
example : S.centroid + ((1 : ℝ) + 2)⁻¹ • (point 6 - S.centroid) = point 4 := by
  rw [centroid_shifted]
  ext i
  fin_cases i
  norm_num [point]

example : simplexCoord S 0
    (S.centroid + ((1 : ℝ) + 2)⁻¹ • (point 6 - S.centroid)) = 0 := by
  have h := simplexCoord_centroid_contraction S 0 (point 6)
  rw [(coord_formula (point 6)).1] at h
  norm_num [point] at h ⊢
  exact h

-- Actual maximality gives a global original-centroid inclusion and literal excess.
example : (body S : Set (Space 1)) ⊆ centeredDilation S 2 := by
  have h := maximumInscribed_centered_bound (le_refl 1) (body S) S (max_self S)
  norm_num at h
  exact h

example : excess (body S : Set (Space 1)) S ≤ 2 := by
  have h := maximumInscribed_excess_le_dim_add_one (le_refl 1) (body S) S (max_self S)
  norm_num at h
  exact h

-- Without maximality, a genuine point of a compact convex body violates the inclusion.
example : ∃ x ∈ (body L : Set (Space 1)), x ∉ centeredDilation S 2 := by
  refine ⟨point 7, subset_convexHull ℝ _ ⟨1, rfl⟩, ?_⟩
  rintro ⟨y, hy, he⟩
  have hnonneg : 0 ≤ simplexCoord S 0 y := by
    change y ∈ convexHull ℝ (Set.range (simplexAffineBasis S)) at hy
    rw [(simplexAffineBasis S).convexHull_eq_nonneg_coord] at hy
    exact hy 0
  rw [(coord_formula y).1] at hnonneg
  have hh := congrArg (fun x : Space 1 => x 0) he
  rw [centroid_shifted] at hh
  change 3 + (1 + 2 : ℝ) * (y 0 - 3) = 7 at hh
  linarith

end CentroidMaximumBoundChecks
