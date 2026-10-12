import Entry005.AffineNormalization
import Mathlib.Tactic.FinCases

noncomputable section
open Entry005 MeasureTheory Metric
open scoped BigOperators Pointwise
namespace HausdorffChecks

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

private def outer := segment (-1) 1 (by norm_num)
private def small := segment (-7 / 8) (7 / 8) (by norm_num)

private theorem outer_ball : closedBall (0 : Space 1) 1 ⊆ simplexSet outer := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm, sub_zero, norm_one, abs_le] at hx
  exact (interval_mem _ _ _ x).mpr hx

private theorem small_hausdorff : hausdorffDist (simplexSet small) (simplexSet outer) ≤ (1 / 8 : ℝ) := by
  apply hausdorffDist_le_of_mem_dist (by norm_num)
  · intro x hx
    have hh := (interval_mem _ _ _ x).mp hx
    refine ⟨x, (interval_mem _ _ _ x).mpr ?_, by norm_num⟩
    constructor <;> linarith
  · intro x hx
    have hh := (interval_mem _ _ _ x).mp hx
    refine ⟨(7 / 8 : ℝ) • x, (interval_mem _ _ _ _).mpr ?_, ?_⟩
    · change -7 / 8 ≤ (7 / 8 : ℝ) * x 0 ∧ (7 / 8 : ℝ) * x 0 ≤ 7 / 8
      constructor <;> linarith
    · rw [dist_eq_norm, norm_one]
      change |x 0 - (7 / 8 : ℝ) * x 0| ≤ 1 / 8
      rw [abs_le]
      constructor <;> linarith

-- The outer body alone has the unit ball; the inner body genuinely lacks it.
example : ¬ closedBall (0 : Space 1) 1 ⊆ simplexSet small := by
  intro h
  have hh := (interval_mem _ _ _ (point 1)).mp (h (by simp [mem_closedBall, dist_eq_norm, norm_one, point]))
  norm_num [point] at hh

example : (1 - (1 / 8 : ℝ)) • simplexSet outer ⊆ simplexSet small := by
  exact shrink_subset_of_hausdorff (simplexBody small) (simplexBody outer) (1 / 8)
    outer_ball (by norm_num) (by norm_num) small_hausdorff

private def translated := segment 2 4 (by norm_num)
private def shortened := segment 2 (15 / 4) (by norm_num)

private theorem translated_hausdorff : hausdorffDist (simplexSet shortened) (simplexSet translated) ≤ (1 / 4 : ℝ) := by
  apply hausdorffDist_le_of_mem_dist (by norm_num)
  · intro x hx
    have hh := (interval_mem _ _ _ x).mp hx
    refine ⟨x, (interval_mem _ _ _ x).mpr ?_, by norm_num⟩
    constructor <;> linarith
  · intro x hx
    have hh := (interval_mem _ _ _ x).mp hx
    by_cases h : x 0 ≤ 15 / 4
    · exact ⟨x, (interval_mem _ _ _ x).mpr ⟨hh.1, h⟩, by norm_num⟩
    · refine ⟨point (15 / 4), (interval_mem _ _ _ _).mpr (by norm_num [point]), ?_⟩
      rw [dist_eq_norm, norm_one]
      change |x 0 - 15 / 4| ≤ 1 / 4
      rw [abs_le]
      constructor <;> linarith

-- A real small Hausdorff gap without the unit-ball premise does not give origin shrink.
example : ¬ (1 - (1 / 4 : ℝ)) • simplexSet translated ⊆ simplexSet shortened := by
  intro h
  have hp : point 2 ∈ simplexSet translated := (interval_mem _ _ _ _).mpr (by norm_num [point])
  have hh := (interval_mem _ _ _ _).mp (h ⟨point 2, hp, rfl⟩)
  change 2 ≤ (1 - (1 / 4 : ℝ)) * 2 ∧ _ at hh
  norm_num at hh

example : hausdorffDist (simplexSet shortened) (simplexSet translated) ≤ (1 / 4 : ℝ) :=
  translated_hausdorff

private theorem translated_centroid : translated.centroid = point 3 := by
  have h := translated.centroid_vsub_eq (0 : Space 1)
  ext i
  fin_cases i
  have hh := congrArg (fun x : Space 1 => x 0) h
  norm_num [vsub_eq_sub, translated, segment, point, Fin.sum_univ_succ] at hh ⊢
  exact hh

example : ∃ f : Space 1 ≃ᵃ[ℝ] Space 1,
    (affineSimplex f translated).centroid = 0 ∧ closedBall (0 : Space 1) 1 ⊆ simplexSet (affineSimplex f translated) :=
  exists_centered_unit_normalization translated

example : excess ((simplexAffineEquiv translated outer) '' simplexSet translated)
    (affineSimplex (simplexAffineEquiv translated outer) translated) = excess (simplexSet translated) translated :=
  excess_affine_image translated (simplexAffineEquiv translated outer) _

example : maximumInscribed (affineBody (simplexAffineEquiv translated outer) (simplexBody translated))
    (affineSimplex (simplexAffineEquiv translated outer) translated) := by
  apply (maximumInscribed_affine_iff _ _ _).mpr
  exact ⟨Set.Subset.refl _, fun _ ht => measure_mono ht⟩

-- s=0 uses the same true geometric endpoint and identifies both actual carriers.
example : (simplexBody outer : Set (Space 1)) = simplexSet outer ∧ simplexSet outer = simplexSet outer := by
  exact maximum_simplex_zero_hausdorff (le_refl 1) (simplexBody outer) outer outer 1
    ⟨Set.Subset.refl _, fun _ ht => measure_mono ht⟩ (Set.Subset.refl _)
    (by intro i; rw [norm_one]; fin_cases i <;> norm_num [outer, segment, point])
    outer_ball (by exact hausdorffDist_self_zero)

end HausdorffChecks
