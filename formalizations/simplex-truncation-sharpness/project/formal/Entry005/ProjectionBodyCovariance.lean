import Entry005.ProjectionBodyDirections
import Entry005.ProjectionAffineTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Adapted from the actual OpenAI/math solution AffineCovariance.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The body below is the canonical
Entry005.Targets halfspace intersection. Its equality with the homogeneous
description is proved, and all projection/Haar identities are actual theorems.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Entry005
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual brightness has the genuine determinant/inverse-vector covariance. -/
theorem projectionBrightness_linear_image (L : E ≃ₗ[ℝ] E) (K : Set E) (u : E) :
    projectionBrightness (L '' K) u =
      |LinearMap.det L.toLinearMap| * projectionBrightness K (L.symm u) := by
  by_cases hu : u = 0
  · simp [hu, projectionBrightness]
  rw [projectionBrightness, projectionVolumeSet_linear_image L K u hu, projectionBrightness]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- Determinant of the actual adjoint, via an actual orthonormal matrix. -/
theorem det_adjoint_general (A : E →ₗ[ℝ] E) : LinearMap.det A.adjoint = LinearMap.det A := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis A.adjoint, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simp

/-- Genuine covariance of the exact canonical projection-body carrier. -/
theorem projectionBodySet_linear_image (L : E ≃ₗ[ℝ] E) (K : Set E) :
    projectionBodySet (L '' K) =
      (|LinearMap.det L.toLinearMap| • L.symm.toLinearMap.adjoint) '' projectionBodySet K := by
  have hb := projectionBrightness_linear_image L K
  let c := |LinearMap.det L.toLinearMap|
  have hc : 0 < c := abs_pos.mpr L.isUnit_det'.ne_zero
  ext y
  constructor
  · intro hy
    have hy' := (mem_projectionBodySet_iff_brightness (L '' K) y).mp hy
    let z := c⁻¹ • L.toLinearMap.adjoint y
    refine ⟨z, ?_, ?_⟩
    · apply (mem_projectionBodySet_iff_brightness K z).mpr
      intro u
      have h := hy' (L u)
      rw [hb, L.symm_apply_apply] at h
      change inner ℝ u (c⁻¹ • L.toLinearMap.adjoint y) ≤ projectionBrightness K u
      rw [real_inner_smul_right, LinearMap.adjoint_inner_right]
      calc
        c⁻¹ * inner ℝ (L u) y ≤ c⁻¹ * (c * projectionBrightness K u) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
        _ = projectionBrightness K u := by field_simp
    · change c • L.symm.toLinearMap.adjoint z = y
      have hcancel : L.symm.toLinearMap.adjoint (L.toLinearMap.adjoint y) = y := by
        change (L.symm.toLinearMap.adjoint.comp L.toLinearMap.adjoint) y = y
        rw [← LinearMap.adjoint_comp]
        simp
      simp [z, map_smul, hcancel, smul_smul, hc.ne']
  · rintro ⟨z, hz, rfl⟩
    apply (mem_projectionBodySet_iff_brightness (L '' K) _).mpr
    intro u
    change inner ℝ u (c • L.symm.toLinearMap.adjoint z) ≤ _
    rw [real_inner_smul_right, LinearMap.adjoint_inner_right, hb]
    exact mul_le_mul_of_nonneg_left
      ((mem_projectionBodySet_iff_brightness K z).mp hz (L.symm u)) hc.le

omit [MeasurableSpace E] [BorelSpace E] in
/-- Exact volume factor of the actual contravariant projection-body map. -/
theorem det_projectionBody_transform_general (hd : 1 ≤ Module.finrank ℝ E)
    (L : E ≃ₗ[ℝ] E) :
    |LinearMap.det (|LinearMap.det L.toLinearMap| • L.symm.toLinearMap.adjoint)| =
      |LinearMap.det L.toLinearMap| ^ (Module.finrank ℝ E - 1) := by
  rw [LinearMap.det_smul, det_adjoint_general, LinearEquiv.det_coe_symm,
    abs_mul, abs_pow, abs_abs, abs_inv]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show Module.finrank ℝ E ≠ 0 by omega)
  rw [hk]
  simp [pow_succ, L.isUnit_det'.ne_zero]

/-- Ratio invariance derived from actual projection covariance and Haar image scaling.
All sets are allowed; no invariant-ratio premise or finiteness premise is supplied. -/
theorem projectionRatio_linear_image (hd : 1 ≤ Module.finrank ℝ E)
    (L : E ≃ₗ[ℝ] E) (K : Set E) :
    projectionRatio (L '' K) = projectionRatio K := by
  have hc : |LinearMap.det L.toLinearMap| ≠ 0 := abs_ne_zero.mpr L.isUnit_det'.ne_zero
  have hvol : volume (L '' K) =
      ENNReal.ofReal |LinearMap.det L.toLinearMap| * volume K :=
    volume.addHaar_image_linearMap L.toLinearMap K
  unfold projectionRatio
  rw [projectionBodySet_linear_image, volume.addHaar_image_linearMap,
    det_projectionBody_transform_general hd L, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg _) _), hvol,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hc)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem affine_image_decomp (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    f '' K = (fun x : E => x + f 0) '' (f.linear '' K) := by
  rw [Set.image_image]
  congr 1
  funext x
  exact congrFun f.toAffineMap.decomp x

/-- Actual affine projection-body covariance, including the exact translation. -/
theorem projectionBodySet_affine_image (f : E ≃ᵃ[ℝ] E) (K : Set E) :
    projectionBodySet (f '' K) =
      (|LinearMap.det f.linear.toLinearMap| • f.linear.symm.toLinearMap.adjoint) ''
        projectionBodySet K := by
  rw [affine_image_decomp, projectionBodySet_translate, projectionBodySet_linear_image]

/-- The actual normalized projection ratio is invariant under every genuine affine equivalence. -/
theorem projectionRatio_affine_image (hd : 1 ≤ Module.finrank ℝ E)
    (f : E ≃ᵃ[ℝ] E) (K : Set E) : projectionRatio (f '' K) = projectionRatio K := by
  rw [affine_image_decomp, projectionRatio_translate, projectionRatio_linear_image hd]

end Entry005
