import Entry005.Targets
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Haar volume scales by the genuine determinant for every finite-dimensional real
inner product space and every set, including sets with zero or infinite volume. -/
theorem volume_affine_image_general (f : E ≃ᵃ[ℝ] E) (A : Set E) :
    volume (f '' A) = ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| * volume A := by
  have himage : f '' A = (fun x : E => x + -f 0) ⁻¹' (f.linear '' A) := by
    ext x
    change (∃ y ∈ A, f y = x) ↔ ∃ y ∈ A, f.linear y = x + -f 0
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      change f.linear y = f.toAffineMap y + -f.toAffineMap 0
      rw [congrFun f.toAffineMap.decomp y]
      simp
    · rintro ⟨y, hy, he⟩
      refine ⟨y, hy, ?_⟩
      change f.toAffineMap y = x
      rw [congrFun f.toAffineMap.decomp y, Pi.add_apply]
      change f.linear y + f 0 = x
      rw [he]
      simp
  rw [himage, measure_preimage_add_right]
  exact volume.addHaar_image_linearMap f.linear.toLinearMap A

/-- The invertible linear part of the affine lift: the translation induces a shear. -/
def pyramidLinearEquiv (f : E ≃ᵃ[ℝ] E) : (E × ℝ) ≃ₗ[ℝ] (E × ℝ) where
  toFun p := (f.linear p.1 - p.2 • f 0, p.2)
  invFun p := (f.linear.symm (p.1 + p.2 • f 0), p.2)
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp
  map_add' p q := by
    ext <;> simp [add_smul, sub_add_sub_comm]
  map_smul' r p := by
    ext <;> simp [smul_sub, smul_smul]

/-- Lift `f(x)=Lx+b` to `(x,t) ↦ (Lx+(1-t)b,t)`, fixing the actual apex. -/
def liftedAffineEquiv (f : E ≃ᵃ[ℝ] E) :
    WithLp 2 (E × ℝ) ≃ᵃ[ℝ] WithLp 2 (E × ℝ) :=
  AffineEquiv.ofLinearEquiv
    ((WithLp.linearEquiv 2 ℝ (E × ℝ)).trans
      ((pyramidLinearEquiv f).trans (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm))
    0 (WithLp.toLp 2 (f 0, (0 : ℝ)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem liftedAffineEquiv_apply (f : E ≃ᵃ[ℝ] E) (x : E) (t : ℝ) :
    liftedAffineEquiv f (WithLp.toLp 2 (x, t)) =
      WithLp.toLp 2 (f.linear x + (1 - t) • f 0, t) := by
  simp only [liftedAffineEquiv, AffineEquiv.ofLinearEquiv_apply,
    vsub_eq_sub, vadd_eq_add, sub_zero, LinearEquiv.trans_apply,
    WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv]
  change WithLp.toLp 2 (f.linear x - t • f 0, t) + WithLp.toLp 2 (f 0, 0) = _
  rw [← WithLp.toLp_add]
  congr 1
  ext <;> simp [sub_smul]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual inverse removes the height-dependent translation before applying `L⁻¹`. -/
theorem liftedAffineEquiv_symm_apply (f : E ≃ᵃ[ℝ] E) (y : E) (t : ℝ) :
    (liftedAffineEquiv f).symm (WithLp.toLp 2 (y, t)) =
      WithLp.toLp 2 (f.linear.symm (y - (1 - t) • f 0), t) := by
  apply (liftedAffineEquiv f).injective
  rw [AffineEquiv.apply_symm_apply, liftedAffineEquiv_apply]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem liftedAffineEquiv_base (f : E ≃ᵃ[ℝ] E) (x : E) :
    liftedAffineEquiv f (WithLp.toLp 2 (x, (0 : ℝ))) =
      WithLp.toLp 2 (f x, (0 : ℝ)) := by
  rw [liftedAffineEquiv_apply]
  simp only [sub_zero, one_smul]
  congr 1
  exact Prod.ext (congrFun f.toAffineMap.decomp x).symm rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem liftedAffineEquiv_apex (f : E ≃ᵃ[ℝ] E) :
    liftedAffineEquiv f (WithLp.toLp 2 ((0 : E), (1 : ℝ))) =
      WithLp.toLp 2 ((0 : E), (1 : ℝ)) := by
  rw [liftedAffineEquiv_apply]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Genuine affine images commute with the actual pyramid hull, with apex fixed. -/
theorem pyramidSet_affine_image (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    pyramidSet (f '' K) = liftedAffineEquiv f '' pyramidSet K := by
  unfold pyramidSet
  change convexHull ℝ _ = (liftedAffineEquiv f).toAffineMap '' convexHull ℝ _
  rw [(liftedAffineEquiv f).toAffineMap.image_convexHull]
  congr 1
  change _ = (liftedAffineEquiv f) '' _
  rw [Set.image_union, Set.image_singleton, liftedAffineEquiv_apex,
    Set.image_image, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, liftedAffineEquiv_base f y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (liftedAffineEquiv_base f y).symm⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The lift adds exactly one real dimension. -/
theorem finrank_lifted_space :
    Module.finrank ℝ (WithLp 2 (E × ℝ)) = Module.finrank ℝ E + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The shear block has determinant one in the new direction. -/
theorem pyramidLinearEquiv_det (f : E ≃ᵃ[ℝ] E) :
    LinearMap.det (pyramidLinearEquiv f).toLinearMap =
      LinearMap.det f.linear.toLinearMap := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let c := Module.Basis.singleton Unit ℝ
  let := Module.Free.ChooseBasisIndex.fintype ℝ E
  let B : Matrix (Module.Free.ChooseBasisIndex ℝ E) Unit ℝ := fun i j =>
    LinearMap.toMatrix (b.prod c) (b.prod c) (pyramidLinearEquiv f).toLinearMap
      (Sum.inl i) (Sum.inr j)
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) (pyramidLinearEquiv f).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix b b f.linear.toLinearMap) B 0 1 := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix_apply, pyramidLinearEquiv]
    · rfl
    · simp [LinearMap.toMatrix_apply, pyramidLinearEquiv]
    · simp [LinearMap.toMatrix_apply, pyramidLinearEquiv, c]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, LinearMap.det_toMatrix]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Passing between the product and `WithLp` conjugates the linear map. -/
theorem liftedAffineEquiv_det (f : E ≃ᵃ[ℝ] E) :
    LinearMap.det (liftedAffineEquiv f).linear.toLinearMap =
      LinearMap.det f.linear.toLinearMap := by
  change LinearMap.det
    (((WithLp.linearEquiv 2 ℝ (E × ℝ)).trans
      ((pyramidLinearEquiv f).trans (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm)).toLinearMap) = _
  change LinearMap.det ((WithLp.linearEquiv 2 ℝ (E × ℝ)).symm.toLinearMap ∘ₗ
    (pyramidLinearEquiv f).toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℝ (E × ℝ)).toLinearMap) = _
  calc
    _ = LinearMap.det (pyramidLinearEquiv f).toLinearMap := by
      simpa only [LinearEquiv.symm_symm] using
        LinearMap.det_conj (pyramidLinearEquiv f).toLinearMap
          (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm
    _ = LinearMap.det f.linear.toLinearMap := pyramidLinearEquiv_det f

/-- The actual pyramid volume has the same affine determinant factor as its base. -/
theorem volume_pyramidSet_affine_image (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    volume (pyramidSet (f '' K)) =
      ENNReal.ofReal |LinearMap.det f.linear.toLinearMap| * volume (pyramidSet K) := by
  rw [pyramidSet_affine_image, volume_affine_image_general, liftedAffineEquiv_det]

end Entry005
