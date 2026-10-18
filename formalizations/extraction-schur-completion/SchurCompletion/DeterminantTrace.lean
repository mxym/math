import SchurCompletion.HaarMinorMoments
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Matrix.PosDef

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

theorem sum_le_card_sub_one_add_prod {ι : Type*} (T : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ T, 0 ≤ x i) (h1 : ∀ i ∈ T, x i ≤ 1) :
    (∑ i ∈ T, x i) ≤ (T.card : ℝ)-1 + ∏ i ∈ T, x i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hx0 := h0 a (Finset.mem_insert_self _ _)
    have hx1 := h1 a (Finset.mem_insert_self _ _)
    have ht0 (i) (hi : i ∈ T) := h0 i (Finset.mem_insert_of_mem hi)
    have ht1 (i) (hi : i ∈ T) := h1 i (Finset.mem_insert_of_mem hi)
    have hP0 : 0 ≤ ∏ i ∈ T, x i := Finset.prod_nonneg ht0
    have hP1 : (∏ i ∈ T, x i) ≤ 1 := Finset.prod_le_one₀ ht0 ht1
    have hIH := ih ht0 ht1
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add,
      Nat.cast_one, Finset.prod_insert ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hP1)]

theorem prod_le_arithmetic_mean_pow (s : ℕ) (hs : 0 < s) (x : Fin s → ℝ)
    (h0 : ∀ i, 0 ≤ x i) :
    (∏ i, x i) ≤ ((∑ i, x i)/(s : ℝ))^s := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin s => (1 : ℝ)) x
    (by intro i hi; norm_num) (by simpa using hsR) (by intro i hi; exact h0 i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hp : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i hi => h0 i)
  calc
    _ = ((∏ i, x i) ^ (s : ℝ)⁻¹)^s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp, inv_mul_cancel₀ hsR.ne', Real.rpow_one]
    _ ≤ _ := by gcongr

theorem contraction_eigenvalues_le_one {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ)
    (hG : G.PosSemidef) (hI : (1-G).PosSemidef) (i : Fin s) :
    hG.isHermitian.eigenvalues i ≤ 1 := by
  let W := hG.isHermitian.eigenvectorUnitary
  have he : (W : Matrix (Fin s) (Fin s) ℂ)ᴴ * G *
      (W : Matrix (Fin s) (Fin s) ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hG.isHermitian.eigenvalues) := by
    simpa only [W, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Function.comp_def] using
      hG.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hh := hI.conjTranspose_mul_mul_same (W : Matrix (Fin s) (Fin s) ℂ)
  have hW : (W : Matrix (Fin s) (Fin s) ℂ)ᴴ * (W : Matrix (Fin s) (Fin s) ℂ) = 1 := W.prop.1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hW, he] at hh
  have hd := hh.diag_nonneg (i := i)
  have hr := (RCLike.nonneg_iff.mp hd).1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at hr
  change 0 ≤ 1-hG.isHermitian.eigenvalues i at hr
  linarith

theorem contraction_det_trace_bounds (s : ℕ) (hs : 0 < s)
    (G : Matrix (Fin s) (Fin s) ℂ) (hG : G.PosSemidef) (hI : (1-G).PosSemidef) :
    G.trace.re ≤ (s : ℝ)-1 + G.det.re ∧
      G.det.re ≤ (G.trace.re/(s : ℝ))^s := by
  have ht : G.trace.re = ∑ i, hG.isHermitian.eigenvalues i := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have hd : G.det.re = ∏ i, hG.isHermitian.eigenvalues i := by
    rw [hG.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [ht, hd]
  constructor
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      sum_le_card_sub_one_add_prod Finset.univ hG.isHermitian.eigenvalues
        (fun i hi => hG.eigenvalues_nonneg i)
        (fun i hi => contraction_eigenvalues_le_one G hG hI i)
  · exact prod_le_arithmetic_mean_pow s hs _ (hG.eigenvalues_nonneg)


def projectedGram (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    Matrix (Fin s) (Fin s) ℂ :=
  ((U : Matrix (Fin D) (Fin D) ℂ) * coordinateRankProjection D s hsD *
    (U : Matrix (Fin D) (Fin D) ℂ)ᴴ).submatrix
      (coordinateLetterEmbedding hsD) (coordinateLetterEmbedding hsD)

theorem projectedGram_eq_minor_gram (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    projectedGram D s hsD U = principalMinor D s hsD U * (principalMinor D s hsD U)ᴴ := by
  let C := Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)
  let B := (U : Matrix (Fin D) (Fin D) ℂ) * C
  have hQ : (U : Matrix (Fin D) (Fin D) ℂ) * coordinateRankProjection D s hsD *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = B*Bᴴ := by
    simp only [B, C, coordinateRankProjection, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hB : B.submatrix (coordinateLetterEmbedding hsD) id = principalMinor D s hsD U := by
    ext i j
    simp [B, C, principalMinor, Matrix.mul_apply, Extraction.coordinateIsometry]
  rw [projectedGram, hQ]
  change B.submatrix (coordinateLetterEmbedding hsD) id *
    (B.submatrix (coordinateLetterEmbedding hsD) id)ᴴ = _
  rw [hB]

theorem projectedGram_contraction (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    (projectedGram D s hsD U).PosSemidef ∧ (1-projectedGram D s hsD U).PosSemidef := by
  let P := coordinateRankProjection D s hsD
  have hP : P.IsHermitian := coordinateRankProjection_isHermitian D s hsD
  have hPP : P*P=P := coordinateRankProjection_idempotent D s hsD
  have hcomp : (1-P).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose (1-P)
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP,
      sub_sub_cancel, sub_self, sub_zero] using h
  constructor
  · rw [projectedGram_eq_minor_gram]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · have h := hcomp.mul_mul_conjTranspose_same (U : Matrix (Fin D) (Fin D) ℂ)
    have hU : (U : Matrix (Fin D) (Fin D) ℂ) * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := U.prop.2
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] at h
    have hsub : (1 : Matrix (Fin D) (Fin D) ℂ).submatrix
        (coordinateLetterEmbedding hsD) (coordinateLetterEmbedding hsD) = 1 := by
      ext i j
      simp [Matrix.one_apply, (coordinateLetterEmbedding hsD).injective.eq_iff]
    have hh := h.submatrix (coordinateLetterEmbedding hsD)
    simpa only [Matrix.submatrix_sub, Pi.sub_apply, hsub, projectedGram, P] using hh

def projectionOverlap (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) : ℝ :=
  (coordinateRankProjection D s hsD *
    ((U : Matrix (Fin D) (Fin D) ℂ) * coordinateRankProjection D s hsD *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace.re

theorem projectedGram_trace (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    (projectedGram D s hsD U).trace.re = projectionOverlap D s hsD U := by
  rw [projectionOverlap, coordinateRankProjection_trace_entries]
  rfl

theorem projectedGram_det (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    (projectedGram D s hsD U).det.re = Complex.normSq (principalMinor D s hsD U).det := by
  rw [projectedGram_eq_minor_gram, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- Actual determinant/trace bounds for genuine unitary principal minors and
genuine rank-s projection overlap. These give the two pointwise sides needed
to transfer rectangular minor moments to the actual Haar purity. -/
theorem principalMinor_projectionOverlap_bounds (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D)
    (U : OneCopyUnitary D) :
    projectionOverlap D s hsD U ≤ (s : ℝ)-1 + Complex.normSq (principalMinor D s hsD U).det ∧
      Complex.normSq (principalMinor D s hsD U).det ≤
        (projectionOverlap D s hsD U/(s : ℝ))^s := by
  have hG := projectedGram_contraction D s hsD U
  have h := contraction_det_trace_bounds s hs (projectedGram D s hsD U) hG.1 hG.2
  simpa only [projectedGram_trace, projectedGram_det] using h

end
end ExtractionSchur
