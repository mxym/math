import Entry005.TruncationFacetGeometry
import Entry005.FiniteHalfspaceCauchy
import Entry005.IntrinsicLinearImageReuse

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Entry005

/-- Deleting coordinate `i` gives genuine orthonormal coordinates in the
coordinate facet's supporting hyperplane. -/
def truncationCoordinateIsometry {d : ℕ} (i : Fin (d + 1)) :
    Space d ≃ₗᵢ[ℝ] (ℝ ∙ (-truncationVertex i))ᗮ where
  toFun x := ⟨WithLp.toLp 2 (i.insertNth 0 (fun j => x j)), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [inner_neg_left]
    change -inner ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i) _ = 0
    rw [EuclideanSpace.basisFun_inner]
    simp⟩
  invFun y := WithLp.toLp 2 (i.removeNth (fun j => (y : Space (d + 1)) j))
  left_inv x := by
    apply PiLp.ext
    intro j
    simp [Fin.removeNth]
  right_inv y := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    have hy : (y : Space (d + 1)) i = 0 := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
      rw [inner_neg_left] at h
      change -inner ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i) _ = 0 at h
      rw [EuclideanSpace.basisFun_inner] at h
      exact neg_eq_zero.mp h
    have heq : i.insertNth 0 (i.removeNth (fun k => (y : Space (d + 1)) k)) =
        (fun k => (y : Space (d + 1)) k) :=
      Fin.insertNth_eq_iff.mpr ⟨hy.symm, rfl⟩
    exact congrFun heq j
  map_add' x y := by
    apply Subtype.ext
    apply PiLp.ext
    change ∀ k, i.insertNth (α := fun _ => ℝ) 0 (fun j => (x + y) j) k =
      i.insertNth (α := fun _ => ℝ) 0 (fun j => x j) k +
        i.insertNth (α := fun _ => ℝ) 0 (fun j => y j) k
    rw [Fin.forall_iff_succAbove i]
    constructor
    · simp
    · intro j
      simp
  map_smul' a x := by
    apply Subtype.ext
    apply PiLp.ext
    change ∀ k, i.insertNth (α := fun _ => ℝ) 0 (fun j => (a • x) j) k =
      a * i.insertNth (α := fun _ => ℝ) 0 (fun j => x j) k
    rw [Fin.forall_iff_succAbove i]
    constructor
    · simp
    · intro j
      simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (i.insertNth 0 (fun j => x j)) : Space (d + 1))‖ ^ 2 = ‖x‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succAbove _ i]
    simp

@[simp] theorem truncationCoordinateIsometry_val {d : ℕ} (i : Fin (d + 1))
    (x : Space d) :
    (truncationCoordinateIsometry i x : Space (d + 1)) =
      WithLp.toLp 2 (i.insertNth 0 (fun j => x j)) := rfl

@[simp] theorem truncation_coordinate_isometry_sum {d : ℕ} (i : Fin (d + 1))
    (x : Space d) :
    ∑ j, (truncationCoordinateIsometry i x : Space (d + 1)) j = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- The actual coordinate facet is the lower-dimensional actual truncation,
with the induced Euclidean measure, through an explicit linear isometry. -/
theorem truncation_coordinate_isometry_mem {d : ℕ} (i : Fin (d + 1))
    (x : Space d) (t : ℝ) :
    (truncationCoordinateIsometry i x : Space (d + 1)) ∈ truncationSet (d + 1) t ↔
      x ∈ truncationSet d t := by
  change ((∀ j, 0 ≤ (truncationCoordinateIsometry i x : Space (d + 1)) j) ∧
    t ≤ ∑ j, (truncationCoordinateIsometry i x : Space (d + 1)) j ∧
      ∑ j, (truncationCoordinateIsometry i x : Space (d + 1)) j ≤ 1) ↔ _
  rw [truncation_coordinate_isometry_sum]
  simp only [truncationCoordinateIsometry_val,
    Fin.forall_iff_succAbove i, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, le_refl, true_and]
  rfl

theorem truncation_coordinate_facet_chart {d : ℕ} (i : Fin (d + 1)) (t : ℝ) :
    finiteHalfspaceFacetChart (truncationFacetNormal (d + 1))
      (truncationFacetHeight (d + 1) t) (Sum.inl i) =
        truncationCoordinateIsometry i '' truncationSet d t := by
  ext y
  obtain ⟨x, rfl⟩ := (truncationCoordinateIsometry i).surjective y
  change (0 : ℝ) • (-truncationVertex i) +
    (truncationCoordinateIsometry i x : Space (d + 1)) ∈
      finiteHalfspaceSet (truncationFacetNormal (d + 1))
        (truncationFacetHeight (d + 1) t) ↔ _
  rw [zero_smul, zero_add, truncation_halfspace_representation (Nat.zero_lt_succ d),
    truncation_coordinate_isometry_mem]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have heq := (truncationCoordinateIsometry i).injective hzx
    subst z
    exact hz

/-- Intrinsic area of the literal coordinate facet in dimension `d + 1`.
The Euclidean volume calculation is inherited through the proved isometry;
there is no geometric Jacobian or facet-volume assumption. -/
theorem truncation_coordinate_facet_area_succ {d : ℕ} (hd : 0 < d)
    (i : Fin (d + 1)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal (d + 1))
      (truncationFacetHeight (d + 1) t) (Sum.inl i) =
        (1 - t ^ d) / (d.factorial : ℝ) := by
  unfold finiteHalfspaceFacetArea
  rw [truncation_coordinate_facet_chart]
  change (volume (truncationCoordinateIsometry i '' truncationSet d t)).toReal = _
  rw [IntrinsicLinearImageReuse.isometry_volume_image,
    truncation_actual_volume hd t ht0 ht1]

/-- Actual coordinate-facet area in every ambient dimension at least two,
including the two-dimensional segment case. -/
theorem truncation_coordinate_facet_area {d : ℕ} (hd : 2 ≤ d)
    (i : Fin d) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteHalfspaceFacetArea (truncationFacetNormal d)
      (truncationFacetHeight d t) (Sum.inl i) =
        (1 - t ^ (d - 1)) / ((d - 1).factorial : ℝ) := by
  cases d with
  | zero => omega
  | succ d =>
    have hpos : 0 < d := by omega
    simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using
      truncation_coordinate_facet_area_succ hpos i t ht0 ht1

#print axioms truncationCoordinateIsometry
#print axioms truncationCoordinateIsometry_val
#print axioms truncation_coordinate_isometry_sum
#print axioms truncation_coordinate_isometry_mem
#print axioms truncation_coordinate_facet_chart
#print axioms truncation_coordinate_facet_area_succ
#print axioms truncation_coordinate_facet_area

end Entry005
