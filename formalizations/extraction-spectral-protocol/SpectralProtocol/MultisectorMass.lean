import SpectralProtocol.WeightedBlocks

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A finite orthogonal family of actual source projections admits one
original-space unitary and a complete pair of local channels. Every input
commuting with their total support obeys the full weighted mass lower bound.
All logical factors, code embeddings and decoders are constructed internally. -/
theorem finite_multisector_projection_mass_lower
    (a b a₀ b₀ K J : ℕ) (hK : 0 < K)
    (d : Fin J → ℕ) (hd : ∀ j,0 < d j) (hdk : ∀ j,d j ≤ K)
    (ha : J*a₀ ≤ a) (hb : J*b₀ ≤ b)
    (P : Fin J → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hP : ∀ j,(P j).IsHermitian) (hPP : ∀ j,P j*P j=P j)
    (horth : ∀ j l,j≠l → P j*P l=0)
    (hr : ∀ j,(P j).rank ≤ (a₀/d j)*(b₀/d j)) :
    ∃ (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ)
      (A : (Fin J×(Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀))⊕Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : (Fin J×(Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀))⊕Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ t,(A t)ᴴ*A t=1) ∧ (∑ t,(B t)ᴴ*B t=1) ∧
      ∀ X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ,X.PosSemidef →
        (∑ j,P j)*X=X*(∑ j,P j) →
        (∑ j,((d j:ℝ)/K)*(P j*X).trace.re) ≤
          (Extraction.bellProjector (d := Fin K)*
            Extraction.krausApply (Extraction.productKraus A B)
              ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*X*
                (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)).trace.re := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  choose κ iκ eκ C hC hCP hcard using
    fun j => Extraction.exists_projection_factor (P j) (hP j) (hPP j)
  letI : ∀ j,Fintype (κ j) := iκ
  letI : ∀ j,DecidableEq (κ j) := eκ
  have hCorth := projection_factors_orthogonal P C hC hCP horth
  have hrC (j : Fin J) : Fintype.card (κ j) ≤ (a₀/d j)*(b₀/d j) := by
    rw [hcard j]
    exact hr j
  obtain ⟨U,A,B,hA,hB,hdecode,hoff⟩ :=
    exists_common_multisector_decoder a b a₀ b₀ K J hK d hd hdk ha hb κ C hC hCorth hrC
  refine ⟨U,A,B,hA,hB,?_⟩
  intro X hX hcomm
  let F := physicalChannelLinearMap (Extraction.productKraus A B) U
  have hF (Y : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hY : Y.PosSemidef) :
      (F Y).PosSemidef := physicalChannelLinearMap_posSemidef _ _ _ hY
  have hcomC : (∑ j,C j*(C j)ᴴ)*X=X*(∑ j,C j*(C j)ᴴ) := by
    simpa only [hCP,F,physicalChannelLinearMap,LinearMap.coe_mk,AddHom.coe_mk] using hcomm
  have h := channel_weighted_block_lower F hF
    (Extraction.bellProjector (d := Fin K)) (Extraction.bellProjector_density (d := Fin K)).1
    C hC hCorth (fun j => (d j:ℝ)/K) hdecode hoff X hX hcomC
  simpa only [hCP,F,physicalChannelLinearMap,LinearMap.coe_mk,AddHom.coe_mk] using h

end SpectralProtocol