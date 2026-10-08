import Entry005.PyramidHalfspaces

noncomputable section
open scoped RealInnerProductSpace
namespace Entry005
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal coordinates within the lifted side hyperplane. -/
def pyramidSideFrameLinear (n : E) (h : ℝ) (hn : ‖n‖ = 1) :
    WithLp 2 ((ℝ ∙ n)ᗮ × ℝ) →ₗ[ℝ] (ℝ ∙ pyramidSideNormal n h)ᗮ where
  toFun p := ⟨WithLp.toLp 2 ((p.ofLp.1 : E) + (p.ofLp.2 / pyramidSlope h * h) • n,
      -p.ofLp.2 / pyramidSlope h), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_pyramidSideNormal]
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hn,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.ofLp.1.property]
    ring_nf⟩
  map_add' p q := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change ((p.ofLp.1 : E) + (q.ofLp.1 : E) +
      ((p.ofLp.2 + q.ofLp.2) / pyramidSlope h * h) • n,
      -(p.ofLp.2 + q.ofLp.2) / pyramidSlope h) =
      ((p.ofLp.1 : E) + (p.ofLp.2 / pyramidSlope h * h) • n +
        ((q.ofLp.1 : E) + (q.ofLp.2 / pyramidSlope h * h) • n),
        -p.ofLp.2 / pyramidSlope h + -q.ofLp.2 / pyramidSlope h)
    apply Prod.ext
    · simp only [add_div, add_mul, add_smul]
      module
    · ring
  map_smul' a p := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change (a • (p.ofLp.1 : E) + (a * p.ofLp.2 / pyramidSlope h * h) • n,
      -(a * p.ofLp.2) / pyramidSlope h) =
      (a • ((p.ofLp.1 : E) + (p.ofLp.2 / pyramidSlope h * h) • n),
      a * (-p.ofLp.2 / pyramidSlope h))
    apply Prod.ext
    · simp only [smul_add, smul_smul]
      module
    · ring

@[simp] theorem pyramidSideFrameLinear_val (n : E) (h : ℝ) (hn : ‖n‖ = 1)
    (q : (ℝ ∙ n)ᗮ) (w : ℝ) :
    (pyramidSideFrameLinear n h hn (WithLp.toLp 2 (q, w)) : WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 ((q : E) + (w / pyramidSlope h * h) • n, -w / pyramidSlope h) := rfl

theorem pyramidSideFrameLinear_norm (n : E) (h : ℝ) (hn : ‖n‖ = 1)
    (p : WithLp 2 ((ℝ ∙ n)ᗮ × ℝ)) : ‖pyramidSideFrameLinear n h hn p‖ = ‖p‖ := by
  obtain ⟨⟨q, w⟩, rfl⟩ := WithLp.toLp_surjective 2 p
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖WithLp.toLp 2 ((q : E) + (w / pyramidSlope h * h) • n,
      -w / pyramidSlope h)‖ ^ 2 = ‖WithLp.toLp 2 (q, w)‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖(q : E) + (w / pyramidSlope h * h) • n‖ ^ 2 + ‖-w / pyramidSlope h‖ ^ 2 =
    ‖(q : E)‖ ^ 2 + ‖w‖ ^ 2
  rw [norm_add_sq_real, inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp q.property, norm_smul,
    Real.norm_eq_abs, hn, mul_one]
  simp only [mul_zero, add_zero, sq_abs, Real.norm_eq_abs]
  have hs : pyramidSlope h ≠ 0 := (pyramidSlope_pos h).ne'
  have hs2 := pyramidSlope_sq h
  field_simp [hs]
  rw [hs2]
  ring

theorem pyramidSideFrameLinear_surjective (n : E) (h : ℝ) (hn : ‖n‖ = 1) :
    Function.Surjective (pyramidSideFrameLinear n h hn) := by
  intro y
  obtain ⟨⟨x, t⟩, hp⟩ := WithLp.toLp_surjective 2 y.val
  have hy := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
  rw [← hp, inner_pyramidSideNormal] at hy
  have heq : inner ℝ n x + h * t = 0 := (div_eq_zero_iff.mp hy).resolve_right
    (pyramidSlope_pos h).ne'
  refine ⟨WithLp.toLp 2 ((ℝ ∙ n)ᗮ.orthogonalProjectionOnto x, -pyramidSlope h * t), ?_⟩
  apply Subtype.ext
  rw [pyramidSideFrameLinear_val, ← hp]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change ((ℝ ∙ n)ᗮ.orthogonalProjectionOnto x : E) +
      (-pyramidSlope h * t / pyramidSlope h * h) • n = x
    have hd := unit_normal_projection_decomposition n x hn
    have hc : -pyramidSlope h * t / pyramidSlope h * h = inner ℝ n x := by
      field_simp [(pyramidSlope_pos h).ne']
      nlinarith
    rw [hc]
    exact hd.symm
  · change -(-pyramidSlope h * t) / pyramidSlope h = t
    field_simp [(pyramidSlope_pos h).ne']

def pyramidSideFrame (n : E) (h : ℝ) (hn : ‖n‖ = 1) :
    WithLp 2 ((ℝ ∙ n)ᗮ × ℝ) ≃ₗᵢ[ℝ] (ℝ ∙ pyramidSideNormal n h)ᗮ :=
  LinearIsometryEquiv.ofSurjective
    ⟨pyramidSideFrameLinear n h hn, pyramidSideFrameLinear_norm n h hn⟩
    (pyramidSideFrameLinear_surjective n h hn)

@[simp] theorem pyramidSideFrame_val (n : E) (h : ℝ) (hn : ‖n‖ = 1)
    (q : (ℝ ∙ n)ᗮ) (w : ℝ) :
    (pyramidSideFrame n h hn (WithLp.toLp 2 (q, w)) : WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 ((q : E) + (w / pyramidSlope h * h) • n, -w / pyramidSlope h) := rfl

end Entry005
