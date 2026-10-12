import Entry005.PyramidHalfspaces

noncomputable section
open MeasureTheory Module
open scoped RealInnerProductSpace Pointwise
namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pyramidBaseIsometry : E ≃ₗᵢ[ℝ] (ℝ ∙ (pyramidBaseNormal : WithLp 2 (E × ℝ)))ᗮ where
  toFun x := ⟨WithLp.toLp 2 (x, 0), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_pyramidBaseNormal]
    simp⟩
  invFun y := y.val.ofLp.1
  left_inv x := rfl
  right_inv y := by
    apply Subtype.ext
    change WithLp.toLp 2 (y.val.ofLp.1, (0 : ℝ)) = y.val
    have hy := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
    obtain ⟨⟨x, t⟩, hp⟩ := WithLp.toLp_surjective 2 y.val
    rw [← hp, inner_pyramidBaseNormal] at hy
    rw [← hp]
    apply WithLp.ofLp_injective
    change (x, 0) = (x, t)
    have ht : t = 0 := by linarith
    rw [ht]
  map_add' x y := by
    apply Subtype.ext
    change WithLp.toLp 2 (x + y, (0 : ℝ)) = WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (y, 0)
    rw [← WithLp.toLp_add]
    simp
  map_smul' a x := by
    apply Subtype.ext
    change WithLp.toLp 2 (a • x, (0 : ℝ)) = a • WithLp.toLp 2 (x, 0)
    rw [← WithLp.toLp_smul]
    simp
  norm_map' x := by
    change ‖WithLp.toLp 2 (x, (0 : ℝ))‖ = ‖x‖
    exact WithLp.norm_toLp_fst 2 E ℝ x

@[simp] theorem pyramidBaseIsometry_val (x : E) :
    (pyramidBaseIsometry x : WithLp 2 (E × ℝ)) = WithLp.toLp 2 (x, 0) := rfl

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem pyramid_base_facet_chart (n : ι → E) (h : ι → ℝ) :
    finiteHalfspaceFacetChart (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) none =
      pyramidBaseIsometry '' finiteHalfspaceSet n h := by
  ext y
  obtain ⟨x, rfl⟩ := pyramidBaseIsometry.surjective y
  change (0 : ℝ) • pyramidBaseNormal + WithLp.toLp 2 (x, 0) ∈
      finiteHalfspaceSet (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) ↔ _
  rw [zero_smul, zero_add, mem_pyramidHalfspace_iff]
  simp only [mul_zero, add_zero, le_refl, true_and]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hzx := pyramidBaseIsometry.injective heq
    subst z
    exact hz

section Volume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [Fintype ι] in
/-- The base area is the actual intrinsic hyperplane Haar volume. -/
theorem pyramid_base_facet_area (n : ι → E) (h : ι → ℝ) :
    finiteHalfspaceFacetArea (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) none =
      (volume (finiteHalfspaceSet n h)).toReal := by
  unfold finiteHalfspaceFacetArea
  rw [pyramid_base_facet_chart]
  change (volume (pyramidBaseIsometry '' finiteHalfspaceSet n h)).toReal = _
  rw [IntrinsicLinearImageReuse.isometry_volume_image]

end Volume
end Entry005
