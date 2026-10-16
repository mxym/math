import SpectralProtocol.ResetMixture

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- The same original unitary and complete local channels simultaneously give
quarter of the multisector mass bound and a reset baseline on every input.
The randomization is entirely in the local channels after the sole unitary. -/
theorem finite_multisector_uniform_baseline_lower
    (a b a₀ b₀ K J : ℕ) (hK : 0 < K)
    (d : Fin J → ℕ) (hd : ∀ j,0 < d j) (hdk : ∀ j,d j ≤ K)
    (ha : J*a₀ ≤ a) (hb : J*b₀ ≤ b)
    (P : Fin J → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hP : ∀ j,(P j).IsHermitian) (hPP : ∀ j,P j*P j=P j)
    (horth : ∀ j l,j≠l → P j*P l=0)
    (hr : ∀ j,(P j).rank ≤ (a₀/d j)*(b₀/d j)) :
    ∃ (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ)
      (A : ((Fin J×(Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀))⊕Fin a)⊕Fin a →
        Matrix (Fin K) (Fin a) ℂ)
      (B : ((Fin J×(Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀))⊕Fin b)⊕Fin b →
        Matrix (Fin K) (Fin b) ℂ),
      (∑ t,(A t)ᴴ*A t=1) ∧ (∑ t,(B t)ᴴ*B t=1) ∧
      ∀ X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ,X.PosSemidef →
        let f := (Extraction.bellProjector (d := Fin K)*
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*X*
              (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)).trace.re
        X.trace.re/(4*K) ≤ f ∧
          ((∑ j,P j)*X=X*(∑ j,P j) →
            (∑ j,((d j:ℝ)/K)*(P j*X).trace.re)/4 ≤ f) := by
  classical
  obtain ⟨U,A,B,hA,hB,hlower⟩ :=
    finite_multisector_projection_mass_lower a b a₀ b₀ K J hK d hd hdk ha hb P hP hPP horth hr
  let o₀ : Fin K := ⟨0,hK⟩
  refine ⟨U,halfMixKraus A (resetKraus o₀),halfMixKraus B (resetKraus o₀),
    halfMixKraus_complete A _ hA (resetKraus_complete o₀),
    halfMixKraus_complete B _ hB (resetKraus_complete o₀),?_⟩
  intro X hX
  dsimp only
  have h := local_half_mix_fidelity_bounds K o₀ A B
    ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*X*
      (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)
    (hX.mul_mul_conjTranspose_same _)
  have hU : (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ*
      (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have ht : ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*X*
      (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ).trace=X.trace := by
    rw [Matrix.trace_mul_cycle,hU,Matrix.one_mul]
  refine ⟨?_,?_⟩
  · simpa only [ht] using h.2
  · intro hcomm
    exact (div_le_div_of_nonneg_right (hlower X hX hcomm) (by norm_num : (0:ℝ) ≤ 4)).trans h.1

end SpectralProtocol