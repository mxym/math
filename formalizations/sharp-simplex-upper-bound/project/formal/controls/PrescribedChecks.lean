import Entry005.PrescribedSimplex
import Mathlib.Tactic.FinCases

noncomputable section
open Entry005 MeasureTheory Metric
open scoped BigOperators Pointwise
namespace PrescribedChecks

private def point (r : ℝ) : Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => r)
private def segment (a b : ℝ) (h : a < b) : Affine.Simplex ℝ (Space 1) 1 :=
  ⟨![point a, point b], affineIndependent_of_ne ℝ (fun he => (ne_of_lt h)
    (congrArg (fun x : Space 1 => x 0) he))⟩

private theorem norm_one (x : Space 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs]

private theorem interval_mem (a b : ℝ) (h : a < b) (x : Space 1) :
    x ∈ simplexSet (segment a b h) ↔ a ≤ x 0 ∧ x 0 ≤ b := by
  constructor
  · have hc : Convex ℝ {x : Space 1 | a ≤ x 0 ∧ x 0 ≤ b} := by
      intro x hx y hy α β hα hβ hab
      change a ≤ x 0 ∧ x 0 ≤ b at hx
      change a ≤ y 0 ∧ y 0 ≤ b at hy
      change a ≤ α * x 0 + β * y 0 ∧ α * x 0 + β * y 0 ≤ b
      constructor
      · calc
          a = α * a + β * a := by rw [← add_mul, hab, one_mul]
          _ ≤ α * x 0 + β * y 0 := add_le_add
            (mul_le_mul_of_nonneg_left hx.1 hα) (mul_le_mul_of_nonneg_left hy.1 hβ)
      · calc
          α * x 0 + β * y 0 ≤ α * b + β * b := add_le_add
            (mul_le_mul_of_nonneg_left hx.2 hα) (mul_le_mul_of_nonneg_left hy.2 hβ)
          _ = b := by rw [← add_mul, hab, one_mul]
    have hv : Set.range (segment a b h).points ⊆ {x : Space 1 | a ≤ x 0 ∧ x 0 ≤ b} := by
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simpa [segment, point] using h.le
    exact fun hx => (convexHull_min hv hc) hx
  · intro hx
    have hden : 0 < b - a := sub_pos.mpr h
    have h0 : point a ∈ simplexSet (segment a b h) := subset_convexHull ℝ _ ⟨0, rfl⟩
    have h1 : point b ∈ simplexSet (segment a b h) := subset_convexHull ℝ _ ⟨1, rfl⟩
    have hsum : (b - x 0) / (b - a) + (x 0 - a) / (b - a) = 1 := by
      field_simp
      ring
    have hc := convex_convexHull ℝ (Set.range (segment a b h).points) h0 h1
      (div_nonneg (sub_nonneg.mpr hx.2) hden.le)
      (div_nonneg (sub_nonneg.mpr hx.1) hden.le) hsum
    have he : ((b - x 0) / (b - a)) • point a + ((x 0 - a) / (b - a)) • point b = x := by
      ext i
      fin_cases i
      change ((b - x 0) / (b - a)) * a + ((x 0 - a) / (b - a)) * b = x 0
      field_simp
      ring
    rwa [he] at hc

private def body (S : Affine.Simplex ℝ (Space 1) 1) : ConvexBody (Space 1) :=
  ⟨simplexSet S, convex_convexHull ℝ _, (Set.finite_range S.points).isCompact_convexHull ℝ,
    ⟨S.points 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩⟩

private theorem max_self (S : Affine.Simplex ℝ (Space 1) 1) : maximumInscribed (body S) S :=
  ⟨Set.Subset.refl _, fun _ ht => measure_mono ht⟩

private def outer := segment (-8 / 7) (8 / 7) (by norm_num)
private def inner := segment (-1) 1 (by norm_num)
private def movedOuter := segment (13 / 7) (29 / 7) (by norm_num)
private def movedInner := segment 2 4 (by norm_num)

private theorem inner_in_outer : simplexSet inner ⊆ simplexSet outer := by
  intro x hx
  have hs := (interval_mem _ _ _ x).mp hx
  apply (interval_mem _ _ _ x).mpr
  constructor <;> nlinarith

private theorem inner_ball : closedBall (0 : Space 1) 1 ⊆ simplexSet inner := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm, sub_zero, norm_one, abs_le] at hx
  exact (interval_mem _ _ _ x).mpr hx

private theorem outer_bound (i) : ‖outer.points i‖ ≤ (8 / 7 : ℝ) := by
  rw [norm_one]
  fin_cases i <;> norm_num [outer, segment, point]

private theorem inner_shrink : (1 - (1 / 8 : ℝ)) • simplexSet outer ⊆ simplexSet inner := by
  rintro x ⟨y, hy, rfl⟩
  have hs := (interval_mem _ _ _ y).mp hy
  apply (interval_mem _ _ _ _).mpr
  change -1 ≤ (1 - (1 / 8 : ℝ)) * y 0 ∧ (1 - (1 / 8 : ℝ)) * y 0 ≤ 1
  constructor <;> nlinarith

-- Nontrivial threshold s=δ=1/8, actual maximum and actual shrinking simplex.
example : (1 - (1 / 8 : ℝ)) ^ 1 ≤
    (volume (simplexSet inner)).toReal / (volume (simplexSet outer)).toReal := by
  have hs : AffineMap.homothety (0 : Space 1) (1 - (1 / 8 : ℝ)) '' simplexSet outer ⊆
      (body inner : Set (Space 1)) := by
    change AffineMap.homothety (0 : Space 1) (1 - (1 / 8 : ℝ)) '' simplexSet outer ⊆ simplexSet inner
    simpa [AffineMap.coe_homothety, vsub_eq_sub, vadd_eq_add, Set.image_smul] using inner_shrink
  exact (maximum_simplex_volume_ratio (le_refl 1) (body inner) outer inner 0 (1 / 8)
    (max_self inner) (by norm_num) (by norm_num) hs).1

example : (body inner : Set (Space 1)) ⊆ (9 / 7 : ℝ) • simplexSet inner := by
  have h := retain_maximum_simplex (le_refl 1) (body inner) outer inner (8 / 7) (1 / 8)
    (max_self inner) inner_in_outer outer_bound inner_ball (by norm_num) (by norm_num) inner_shrink
  norm_num at h ⊢
  exact h

-- Genuine equality endpoint; no centroid or bound assumptions are needed.
example (S : Affine.Simplex ℝ (Space 1) 1) :
    ∃ σ : Equiv.Perm (Fin 2), (∀ j, S.points j = S.points (σ j)) ∧ simplexSet S = simplexSet S := by
  have hpos := (simplexMatrixVolumeInterface 1 (le_refl 1) S S (Set.Subset.refl _)).2.2.2.1
  apply simplex_equal_volume_permutation (le_refl 1) S S (Set.Subset.refl _)
  simp [ne_of_gt hpos]

-- The zero deficit hull endpoint does not divide by δ.
example (P S : Affine.Simplex ℝ (Space 1) 1) (M : ℝ)
    (hsub : simplexSet S ⊆ simplexSet P) (hb : ∀ i, ‖P.points i‖ ≤ M)
    (hball : closedBall (0 : Space 1) 1 ⊆ simplexSet S)
    (hv : 1 ≤ (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal) :
    simplexSet P ⊆ simplexSet S := by
  have hz := simplex_hull_dilation (le_refl 1) P S M 0 hsub
    hb hball (le_refl 0) (by norm_num) (by simpa using hv)
  simpa using hz

-- A translated, prescribed original centroid is 3, not the origin.
private theorem moved_centroid : movedInner.centroid = point 3 := by
  have h := movedInner.centroid_vsub_eq (0 : Space 1)
  ext i
  fin_cases i
  have hh := congrArg (fun x : Space 1 => x 0) h
  norm_num [vsub_eq_sub, movedInner, segment, point, Fin.sum_univ_succ] at hh ⊢
  exact hh

private theorem moved_bound (i) : ‖movedOuter.points i - movedInner.centroid‖ ≤ (8 / 7 : ℝ) := by
  rw [moved_centroid, norm_one]
  fin_cases i <;> norm_num [movedOuter, segment, point]

private theorem moved_ball : closedBall movedInner.centroid 1 ⊆ simplexSet movedInner := by
  intro x hx
  rw [moved_centroid, mem_closedBall, dist_eq_norm, norm_one] at hx
  have h : |x 0 - 3| ≤ 1 := hx
  rw [abs_le] at h
  apply (interval_mem _ _ _ x).mpr
  constructor <;> linarith

private theorem moved_shrink : AffineMap.homothety movedInner.centroid (1 - (1 / 8 : ℝ)) ''
    simplexSet movedOuter ⊆ (body movedInner : Set (Space 1)) := by
  rintro x ⟨y, hy, rfl⟩
  have hs := (interval_mem _ _ _ y).mp hy
  apply (interval_mem _ _ _ _).mpr
  rw [moved_centroid]
  change 2 ≤ (1 - (1 / 8 : ℝ)) * (y 0 - 3) + 3 ∧
    (1 - (1 / 8 : ℝ)) * (y 0 - 3) + 3 ≤ 4
  constructor <;> nlinarith

example : excess (body movedInner : Set (Space 1)) movedInner ≤ (2 / 7 : ℝ) := by
  have hk : (body movedInner : Set (Space 1)) ⊆ simplexSet movedOuter := by
    intro x hx
    have hs := (interval_mem _ _ _ x).mp hx
    apply (interval_mem _ _ _ x).mpr
    constructor <;> nlinarith
  have h := retain_maximum_simplex_excess (le_refl 1) (body movedInner) movedOuter movedInner
    (8 / 7) (1 / 8) (max_self movedInner) hk moved_bound moved_ball
    (by norm_num) (by norm_num) moved_shrink
  norm_num at h ⊢
  exact h

example : movedInner.centroid ≠ (0 : Space 1) := by
  rw [moved_centroid]
  intro h
  have he := congrArg (fun x : Space 1 => x 0) h
  norm_num [point] at he

private theorem augmented_segment (a b : ℝ) (h : a < b) :
    augmentedVertices (segment a b h).points = !![1, 1; a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem threshold_ratio : (volume (simplexSet inner)).toReal /
    (volume (simplexSet outer)).toReal = 7 / 8 := by
  have hd : (simplexBarycentricMatrix outer inner).det = 7 / 8 := by
    norm_num [simplexBarycentricMatrix, outer, inner, augmented_segment,
      Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_succ, Ring.inverse_eq_inv]
    rw [Matrix.det_fin_two]
    norm_num
  have hv := (simplexMatrixVolumeInterface 1 (le_refl 1) outer inner inner_in_outer).2.2.2.2.2.2.2
  rw [hd] at hv
  norm_num at hv
  exact hv.symm

-- Deleting the actual near-volume hypothesis gives a false δ=0 hull inclusion.
example : ¬ simplexSet outer ⊆ (1 + 2 * (8 / 7 : ℝ) * 0) • simplexSet inner := by
  simp only [mul_zero, add_zero, one_smul]
  intro h
  have hx : point (8 / 7) ∈ simplexSet outer := subset_convexHull ℝ _ ⟨1, rfl⟩
  have hi := (interval_mem _ _ _ _).mp (h hx)
  norm_num [point] at hi

-- Maximum-volume optimality is essential, and is not replaced by mere inclusion.
example : ¬ maximumInscribed (body outer) inner := by
  intro hm
  have hs : AffineMap.homothety (0 : Space 1) (1 : ℝ) '' simplexSet outer ⊆ (body outer : Set (Space 1)) := by
    change AffineMap.homothety (0 : Space 1) (1 : ℝ) '' simplexSet outer ⊆ simplexSet outer
    simp
  have h := (maximum_simplex_volume_ratio (le_refl 1) (body outer) outer inner 0 0 hm
    (le_refl 0) (by norm_num) (by simpa using hs)).1
  rw [threshold_ratio] at h
  norm_num at h

private def offcenter := segment (-1) 3 (by norm_num)

-- The literal origin unit ball inclusion does not imply a zero simplex centroid.
example : closedBall (0 : Space 1) 1 ⊆ simplexSet offcenter ∧ offcenter.centroid ≠ 0 := by
  constructor
  · intro x hx
    rw [mem_closedBall, dist_eq_norm, sub_zero, norm_one, abs_le] at hx
    apply (interval_mem _ _ _ x).mpr
    constructor <;> linarith
  · have h := offcenter.centroid_vsub_eq (0 : Space 1)
    have hc : offcenter.centroid = point 1 := by
      ext i
      fin_cases i
      have hh := congrArg (fun x : Space 1 => x 0) h
      norm_num [vsub_eq_sub, offcenter, segment, point, Fin.sum_univ_succ] at hh ⊢
      exact hh
    rw [hc]
    intro hz
    have he := congrArg (fun x : Space 1 => x 0) hz
    norm_num [point] at he

private def farOuter := segment 10 (78 / 7) (by norm_num)
private def farInner := segment 10 11 (by norm_num)

-- Actual near-volume nested simplices can fail origin dilation when the unit ball input is removed.
example : simplexSet farInner ⊆ simplexSet farOuter ∧
    (volume (simplexSet farInner)).toReal / (volume (simplexSet farOuter)).toReal = 7 / 8 ∧
    (∀ i, ‖farOuter.points i‖ ≤ (78 / 7 : ℝ)) ∧
    ¬ simplexSet farOuter ⊆ (1 + 2 * (78 / 7 : ℝ) * (1 / 8)) • simplexSet farInner := by
  have hsub : simplexSet farInner ⊆ simplexSet farOuter := by
    intro x hx
    have hs := (interval_mem _ _ _ x).mp hx
    apply (interval_mem _ _ _ x).mpr
    constructor <;> linarith
  refine ⟨hsub, ?_, ?_, ?_⟩
  · have hd : (simplexBarycentricMatrix farOuter farInner).det = 7 / 8 := by
      norm_num [simplexBarycentricMatrix, farOuter, farInner, augmented_segment,
        Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_succ, Ring.inverse_eq_inv]
      rw [Matrix.det_fin_two]
      norm_num
    have hv := (simplexMatrixVolumeInterface 1 (le_refl 1) farOuter farInner hsub).2.2.2.2.2.2.2
    rw [hd] at hv
    norm_num at hv
    exact hv.symm
  · intro i
    rw [norm_one]
    fin_cases i <;> norm_num [farOuter, segment, point]
  · intro hi
    have hx : point 10 ∈ simplexSet farOuter := subset_convexHull ℝ _ ⟨0, rfl⟩
    obtain ⟨y, hy, he⟩ := hi hx
    have hs := (interval_mem _ _ _ y).mp hy
    have hh := congrArg (fun x : Space 1 => x 0) he
    change (1 + 2 * (78 / 7 : ℝ) * (1 / 8)) * y 0 = 10 at hh
    linarith

end PrescribedChecks
