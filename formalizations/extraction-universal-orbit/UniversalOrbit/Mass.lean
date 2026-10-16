import UniversalOrbit.Projector

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport
namespace UniversalOrbit
noncomputable section

theorem universalProjection_posSemidef (D k : ℕ) (S : Finset (Word D k)) :
    (universalProjection D k S).PosSemidef := by
  simpa only [(universalProjection_hermitian D k S).eq,
    universalProjection_idempotent] using
    Matrix.posSemidef_self_mul_conjTranspose (universalProjection D k S)

theorem universalProjection_tensor_diagonal_one (D k : ℕ) (S : Finset (Word D k))
    (V : Matrix.unitaryGroup (Fin D) ℂ) (w : Word D k) (hw : w ∈ S) :
    ((ExtractionSpectrum.tensorUnitary V k : Matrix (Word D k) (Word D k) ℂ)ᴴ *
      universalProjection D k S * ExtractionSpectrum.tensorUnitary V k) w w = 1 := by
  let W := ExtractionSpectrum.tensorUnitary V k
  have hW : (W : Matrix (Word D k) (Word D k) ℂ)ᴴ * W = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  have hfix := universalProjection_fixes D k S _
    (tensorAction_single_mem_universalSpace S w hw (V : Matrix (Fin D) (Fin D) ℂ))
  change universalProjection D k S *ᵥ
    ((W : Matrix (Word D k) (Word D k) ℂ) *ᵥ Pi.single w 1) =
    (W : Matrix (Word D k) (Word D k) ℂ) *ᵥ Pi.single w 1 at hfix
  have h := congrArg (fun v => ((W : Matrix (Word D k) (Word D k) ℂ)ᴴ *ᵥ v) w) hfix
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h
  rw [hW] at h
  simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col,
    Matrix.transpose_apply, Matrix.one_apply_eq] using h

/-- The single fixed orbit projector captures at least the spectral iid mass
of S for every actual density, even when its eigenbasis is unknown. -/
theorem universalProjection_mass_ge (D k : ℕ) (S : Finset (Word D k))
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    (∑ w ∈ S, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w) ≤
      (universalProjection D k S * ExtractionSpectrum.tensorMatrix X k).trace.re := by
  let V := ExtractionSpectrum.tensorUnitary hX.1.isHermitian.eigenvectorUnitary k
  let Q := (V : Matrix (Word D k) (Word D k) ℂ)ᴴ * universalProjection D k S * V
  have hQ : Q.PosSemidef := (universalProjection_posSemidef D k S).conjTranspose_mul_mul_same _
  have hp (w : Word D k) : 0 ≤ ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w :=
    ExtractionSpectrum.iidLaw_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) k w
  have hdiag (w : Word D k) : 0 ≤ (Q w w).re := (RCLike.nonneg_iff.mp hQ.diag_nonneg).1
  have hdiag1 (w : Word D k) (hw : w ∈ S) : (Q w w).re = 1 := by
    dsimp only [Q, V]
    rw [universalProjection_tensor_diagonal_one D k S hX.1.isHermitian.eigenvectorUnitary w hw,
      Complex.one_re]
  have hpair : (universalProjection D k S * ExtractionSpectrum.tensorMatrix X k).trace.re =
      ∑ w, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w * (Q w w).re := by
    rw [ExtractionSpectrum.tensorMatrix_spectral X hX.1.isHermitian k,
      Extraction.trace_congruence_diagonal]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  rw [hpair]
  calc
    _ = ∑ w ∈ S, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w * (Q w w).re := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hdiag1 w hw, mul_one]
    _ ≤ ∑ w, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w * (Q w w).re :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => mul_nonneg (hp w) (hdiag w))

end
end UniversalOrbit
