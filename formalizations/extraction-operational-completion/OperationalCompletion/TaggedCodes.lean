import OperationalCompletion.ProductSum

open scoped BigOperators ComplexOrder Kronecker
open Matrix SpectralProtocol
namespace OperationalCompletion
noncomputable section

/-- Actual packed codes and one complete local decoder on tagged coordinates.
These coordinates will be embedded into a small reserved part of each original
local system alongside the large pure-state sector. -/
theorem exists_tagged_packed_codes (a₀ b₀ K J : ℕ) (hK : 0<K)
    (d : Fin J → ℕ) (hd : ∀ j,0<d j) (hdk : ∀ j,d j≤K)
    (κ : Fin J → Type*) [∀ j,Fintype (κ j)] [∀ j,DecidableEq (κ j)]
    (hr : ∀ j,Fintype.card (κ j)≤(a₀/d j)*(b₀/d j)) :
    ∃ (F : ∀ j,Matrix ((Fin J×Fin a₀)×(Fin J×Fin b₀)) (κ j) ℂ)
      (A : Fin J×(Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀) → Matrix (Fin K) (Fin J×Fin a₀) ℂ)
      (B : Fin J×(Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀) → Matrix (Fin K) (Fin J×Fin b₀) ℂ),
      (∀ j,(F j)ᴴ*F j=1) ∧
      (∀ j l,j≠l → (F j)ᴴ*F l=0) ∧
      (∑ t,(A t)ᴴ*A t=1) ∧ (∑ t,(B t)ᴴ*B t=1) ∧
      (∀ j (Y : Matrix (κ j) (κ j) ℂ),Y.PosSemidef →
        ((d j:ℝ)/K)*Y.trace.re≤(Extraction.bellProjector (d:=Fin K)*
          Extraction.krausApply (Extraction.productKraus A B) (F j*Y*(F j)ᴴ)).trace.re) ∧
      (∀ j l,j≠l → ∀ Y : Matrix (κ j) (κ l) ℂ,
        Extraction.krausApply (Extraction.productKraus A B) (F j*Y*(F l)ᴴ)=0) := by
  classical
  choose E A B hE hA hB hdecode using
    fun j => exists_packed_isometry_decoder a₀ b₀ (d j) K (hd j) (hdk j) (κ j) (hr j)
  let S := fun j : Fin J => productSectorEmbedding (α:=Fin a₀) (β:=Fin b₀) j
  let F := fun j => S j*E j
  have hF (j : Fin J) : (F j)ᴴ*F j=1 :=
    Extraction.isometry_mul _ _ (productSectorEmbedding_isometry j) (hE j)
  have hForth (j l : Fin J) (hjl : j≠l) : (F j)ᴴ*F l=0 := by
    have he : (F j)ᴴ*F l=(E j)ᴴ*((S j)ᴴ*S l)*E l := by
      simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he,productSectorEmbedding_cross,if_neg hjl,Matrix.mul_zero,Matrix.zero_mul]
  let γA := Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀
  let γB := Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀
  let fA (j : Fin J) : (Fin (a₀/d j)⊕Fin a₀) ↪ γA :=
    ⟨fun t => ⟨j,t⟩,by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2⟩
  let fB (j : Fin J) : (Fin (b₀/d j)⊕Fin b₀) ↪ γB :=
    ⟨fun t => ⟨j,t⟩,by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2⟩
  let AA := fun j => extendByZero (fA j) (A j)
  let BB := fun j => extendByZero (fB j) (B j)
  have hAA (j : Fin J) : ∑ t,(AA j t)ᴴ*AA j t=1 := extendByZero_kraus_complete _ _ (hA j)
  have hBB (j : Fin J) : ∑ t,(BB j t)ᴴ*BB j t=1 := extendByZero_kraus_complete _ _ (hB j)
  refine ⟨F,sectorKraus AA,sectorKraus BB,hF,hForth,
    sectorKraus_complete AA hAA,sectorKraus_complete BB hBB,?_,?_⟩
  · intro j Y hY
    have he : F j*Y*(F j)ᴴ=S j*(E j*Y*(E j)ᴴ)*(S j)ᴴ := by
      simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he,productSectorKraus_encoded]
    simp only [ite_true]
    rw [productKraus_extendByZero]
    exact hdecode j Y hY
  · intro j l hjl Y
    have he : F j*Y*(F l)ᴴ=S j*(E j*Y*(E l)ᴴ)*(S l)ᴴ := by
      simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he,productSectorKraus_encoded,if_neg hjl]

end
end OperationalCompletion
