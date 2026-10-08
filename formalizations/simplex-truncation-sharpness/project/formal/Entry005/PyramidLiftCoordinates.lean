import Entry005.PyramidProjectionBody
import Entry005.FiniteLawZonotopeMoment
import Entry005.FiniteHalfspaceConeLaw

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005

/-- Height-first determinant coordinates to the literal pyramid product space. -/
def pyramidLiftCoordinates (d : ℕ) : Space (d + 1) ≃ₗᵢ[ℝ] WithLp 2 (Space d × ℝ) where
  toFun x := WithLp.toLp 2 (WithLp.toLp 2 (fun j => x j.succ), x 0)
  invFun p := WithLp.toLp 2 (Fin.cases p.ofLp.2 p.ofLp.1.ofLp)
  left_inv x := by
    ext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply WithLp.ofLp_injective
      rfl
    · rfl
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply WithLp.ofLp_injective
      rfl
    · rfl
  map_smul' a x := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply WithLp.ofLp_injective
      rfl
    · rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖WithLp.toLp 2 (fun j : Fin d => x j.succ)‖ ^ 2 + ‖x 0‖ ^ 2 = ‖x‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    ring

@[simp] theorem pyramidLiftCoordinates_apply (d : ℕ) (x : Fin d → ℝ) (t : ℝ) :
    pyramidLiftCoordinates d (WithLp.toLp 2 (Fin.cases t x)) =
      WithLp.toLp 2 (WithLp.toLp 2 x, t) := rfl

theorem pyramid_lifted_law_generator {ι : Type*} {d : ℕ} (a h : ι → ℝ)
    (n : ι → Space d) (M : ℝ) (hh : ∀ i, h i ≠ 0) (i : ι) :
    pyramidLiftCoordinates d ((a i * h i / M) •
      WithLp.toLp 2 (Fin.cases 1 (finiteConePoint (fun i j => n i j) h i))) =
      (a i / M) • WithLp.toLp 2 (n i, h i) := by
  rw [map_smul]
  change (a i * h i / M) • WithLp.toLp 2
    (WithLp.toLp 2 (fun j => n i j / h i), 1) = _
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply WithLp.ofLp_injective
    funext j
    change a i * h i / M * (n i j / h i) = a i / M * n i j
    field_simp [hh i]
  · change a i * h i / M * 1 = a i / M * h i
    ring

end Entry005
