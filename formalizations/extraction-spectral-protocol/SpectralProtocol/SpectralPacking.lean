import SpectralProtocol.ProjectionState

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A density's selected positive submatrix is extracted without renormalizing
or postselecting it. The same complete channels act on the entire input, and
the positive remainder contributes a nonnegative overlap. -/
theorem finite_projection_positive_submatrix_lower (a b d K : ℕ)
    (hd : 0 < d) (hdk : d ≤ K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a/d)*(b/d)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a/d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ∀ X S : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        S.PosSemidef → (X-S).PosSemidef → P*S*P=S →
        ((d:ℝ)/K) * S.trace.re ≤
          (Extraction.bellProjector (d := Fin K) *
            Extraction.krausApply (Extraction.productKraus A B)
              ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
                (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin K) := ⟨⟨0,lt_of_lt_of_le hd hdk⟩⟩
  obtain ⟨U,A,B,hA,hB,he⟩ := Extraction.finite_projection_exact_extractor a b d hd P hP hPP hr
  let f : Fin d ↪ Fin K := Extraction.cardEmbedding (by simpa only [Fintype.card_fin] using hdk)
  let E := Extraction.coordinateIsometry f
  have hE : Eᴴ * E = 1 := Extraction.coordinateIsometry_isometry f
  let A' := fun j => E * A j
  let B' := fun j => E * B j
  have hproduct : Extraction.productKraus A' B' =
      fun j => (E ⊗ₖ E) * Extraction.productKraus A B j := by
    funext j
    exact Matrix.mul_kronecker_mul E (A j.1) E (B j.2)
  refine ⟨U,A',B',Extraction.postcomposeKraus_complete A hA E hE,
    Extraction.postcomposeKraus_complete B hB E hE,?_⟩
  intro X S hS hR hPS
  have htrace : S.trace = (S.trace.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (RCLike.nonneg_iff.mp hS.trace_nonneg).2
  have hsout : (Extraction.bellProjector (d := Fin K) *
      Extraction.krausApply (Extraction.productKraus A' B')
        ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * S *
          (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re =
        ((d:ℝ)/K)*S.trace.re := by
    rw [hproduct, Extraction.postcomposeKraus_apply, he S hPS, htrace]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Extraction.embedded_bell_overlap]
    simp only [Fintype.card_fin]
    ring
  have hrout := Extraction.positive_product_trace_re
    (Extraction.bellProjector (d := Fin K))
    (Extraction.krausApply (Extraction.productKraus A' B')
      ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * (X-S) *
        (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ))
    (Extraction.bellProjector_density (d := Fin K)).1
    (Extraction.krausApply_posSemidef _ _ (hR.mul_mul_conjTranspose_same _))
  simp only [Matrix.mul_sub, Matrix.sub_mul, Extraction.krausApply_sub,
    Matrix.trace_sub, Complex.sub_re] at hrout
  linarith

end SpectralProtocol