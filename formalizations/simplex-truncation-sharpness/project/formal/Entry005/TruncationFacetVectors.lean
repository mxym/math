import Entry005.TruncationCoordinateFacets
import Entry005.ConeLawFinite

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Entry005

def truncationFacetScale (d : ℕ) : ℝ := 1 / ((d - 1).factorial : ℝ)

/-- These vectors are proved below to be actual facet area times outward unit
normal of the literal coordinate truncation. -/
def truncationRawHorizontal (d : ℕ) (t : ℝ) : TruncationFacetIndex d → Space d
  | Sum.inl i => (-truncationFacetScale d * (1 - t ^ (d - 1))) • truncationVertex i
  | Sum.inr false => truncationFacetScale d • truncationDiagonal d
  | Sum.inr true => (-truncationFacetScale d * t ^ (d - 1)) • truncationDiagonal d

def truncationRawSupport (d : ℕ) (t : ℝ) : TruncationFacetIndex d → ℝ
  | Sum.inl _ => 0
  | Sum.inr false => truncationFacetScale d
  | Sum.inr true => -truncationFacetScale d * t ^ d

def truncationRawLifted (d : ℕ) (t : ℝ) (i : TruncationFacetIndex d) :
    Fin (d + 1) → ℝ :=
  Fin.cons (truncationRawSupport d t i) (fun j => truncationRawHorizontal d t i j)

theorem truncation_facet_scale_sqrt_cancel {d : ℕ} (hd : 0 < d) :
    (Real.sqrt (d : ℝ) / ((d - 1).factorial : ℝ)) * (Real.sqrt (d : ℝ))⁻¹ =
      truncationFacetScale d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hdR).ne'
  calc
    _ = (1 / ((d - 1).factorial : ℝ)) *
        (Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ))⁻¹) := by ring
    _ = truncationFacetScale d := by rw [mul_inv_cancel₀ hs, mul_one]; rfl

theorem truncation_coordinate_area_vector {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : Fin d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inl i) • truncationFacetNormal d (Sum.inl i) =
        (-truncationFacetScale d * (1 - t ^ (d - 1))) • truncationVertex i := by
  rw [truncation_coordinate_facet_area hd i t ht0.le ht1.le, truncationFacetNormal,
    smul_neg, ← neg_smul]
  congr 1
  dsimp [truncationFacetScale]
  ring

theorem truncation_coordinate_area_support {d : ℕ} (t : ℝ) (i : Fin d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inl i) * truncationFacetHeight d t (Sum.inl i) = 0 := by
  rw [truncationFacetHeight, mul_zero]

theorem truncation_top_area_vector {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr false) • truncationFacetNormal d (Sum.inr false) =
        truncationFacetScale d • truncationDiagonal d := by
  rw [truncation_top_facet_area hd t ht0 ht1, truncationFacetNormal,
    truncationUnitDiagonal, smul_smul, truncation_facet_scale_sqrt_cancel hd]

theorem truncation_top_area_support {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr false) * truncationFacetHeight d t (Sum.inr false) =
        truncationFacetScale d := by
  rw [truncation_top_facet_area hd t ht0 ht1, truncationFacetHeight,
    truncation_facet_scale_sqrt_cancel hd]

theorem truncation_bottom_area_vector {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr true) • truncationFacetNormal d (Sum.inr true) =
        (-truncationFacetScale d * t ^ (d - 1)) • truncationDiagonal d := by
  rw [truncation_bottom_facet_area hd t ht0 ht1, truncationFacetNormal,
    truncationUnitDiagonal, smul_neg, smul_smul, ← neg_smul,
    mul_assoc, truncation_facet_scale_sqrt_cancel hd]
  congr 1
  ring

theorem truncation_bottom_area_support {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t)
      (Sum.inr true) * truncationFacetHeight d t (Sum.inr true) =
        -truncationFacetScale d * t ^ d := by
  rw [truncation_bottom_facet_area hd t ht0 ht1, truncationFacetHeight]
  have hpow : t ^ (d - 1) * t = t ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ = -(t ^ (d - 1) * t) * ((Real.sqrt (d : ℝ) /
        ((d - 1).factorial : ℝ)) * (Real.sqrt (d : ℝ))⁻¹) := by ring
    _ = _ := by rw [hpow, truncation_facet_scale_sqrt_cancel hd]; ring

theorem truncation_actual_facet_vector {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : TruncationFacetIndex d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i •
      truncationFacetNormal d i = truncationRawHorizontal d t i := by
  have hpos : 0 < d := by omega
  cases i with
  | inl i => exact truncation_coordinate_area_vector hd t ht0 ht1 i
  | inr i =>
    cases i
    · exact truncation_top_area_vector hpos t ht0 ht1
    · exact truncation_bottom_area_vector hpos t ht0 ht1

theorem truncation_actual_facet_support {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : TruncationFacetIndex d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i *
      truncationFacetHeight d t i = truncationRawSupport d t i := by
  have hpos : 0 < d := by omega
  cases i with
  | inl i => exact truncation_coordinate_area_support t i
  | inr i =>
    cases i
    · exact truncation_top_area_support hpos t ht0 ht1
    · exact truncation_bottom_area_support hpos t ht0 ht1

/-- Pointwise coordinate-array form, for the actual horizontal determinants. -/
theorem truncation_actual_horizontal_row {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : TruncationFacetIndex d) (j : Fin d) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i *
      truncationFacetNormal d i j = truncationRawHorizontal d t i j := by
  have heq := congrArg (fun x : Space d => x j)
    (truncation_actual_facet_vector hd t ht0 ht1 i)
  exact heq

/-- Height-first actual lifted rows, including the negative bottom support;
these are unnormalized geometric data, not probability weights. -/
theorem truncation_actual_lifted_row {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : TruncationFacetIndex d)
    (j : Fin (d + 1)) :
    finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i *
      finiteFacetLift (truncationFacetHeight d t) (fun i k => truncationFacetNormal d i k) i j =
        truncationRawLifted d t i j := by
  induction j using Fin.cases with
  | zero => exact truncation_actual_facet_support hd t ht0 ht1 i
  | succ j => exact truncation_actual_horizontal_row hd t ht0 ht1 i j

#print axioms truncation_facet_scale_sqrt_cancel
#print axioms truncation_coordinate_area_vector
#print axioms truncation_coordinate_area_support
#print axioms truncation_top_area_vector
#print axioms truncation_top_area_support
#print axioms truncation_bottom_area_vector
#print axioms truncation_bottom_area_support
#print axioms truncation_actual_facet_vector
#print axioms truncation_actual_facet_support
#print axioms truncation_actual_horizontal_row
#print axioms truncation_actual_lifted_row

end Entry005
