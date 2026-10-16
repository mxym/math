import SpectralProtocol.JointIsometry
import SpectralProtocol.ProductSectors
import SpectralProtocol.PaddedKraus
import SpectralProtocol.LocalCode

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- One original-space unitary and one complete pair of local channels jointly
read every orthogonal source block at its own feasible Bell dimension. The
actual local target code and decoder are constructed from integer ranks.
No correct-decoder, target-overlap, or common-unitary premise is supplied. -/
theorem exists_common_multisector_decoder (a b a₀ b₀ K J : ℕ) (hK : 0 < K)
    (d : Fin J → ℕ) (hd : ∀ j,0 < d j) (hdk : ∀ j,d j ≤ K)
    (ha : J*a₀ ≤ a) (hb : J*b₀ ≤ b)
    (κ : Fin J → Type*) [∀ j,Fintype (κ j)] [∀ j,DecidableEq (κ j)]
    (C : ∀ j,Matrix (Fin a×Fin b) (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1)
    (hCorth : ∀ j l,j≠l → (C j)ᴴ*C l=0)
    (hr : ∀ j,Fintype.card (κ j) ≤ (a₀/d j)*(b₀/d j)) :
    ∃ (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ)
      (A : (Fin J×(Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀))⊕Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : (Fin J×(Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀))⊕Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ t,(A t)ᴴ*A t=1) ∧ (∑ t,(B t)ᴴ*B t=1) ∧
      (∀ j (Y : Matrix (κ j) (κ j) ℂ),Y.PosSemidef →
        ((d j:ℝ)/K)*Y.trace.re ≤
          (Extraction.bellProjector (d := Fin K)*
            Extraction.krausApply (Extraction.productKraus A B)
              ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*(C j*Y*(C j)ᴴ)*
                (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)).trace.re) ∧
      (∀ j l,j≠l → ∀ Y : Matrix (κ j) (κ l) ℂ,
        Extraction.krausApply (Extraction.productKraus A B)
          ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*(C j*Y*(C l)ᴴ)*
            (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)=0) := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  choose E A B hE hA hB hdecode using
    fun j => exists_packed_isometry_decoder a₀ b₀ (d j) K (hd j) (hdk j) (κ j) (hr j)
  let EA := Extraction.coordinateIsometry (Extraction.cardEmbedding
    (show Fintype.card (Fin J×Fin a₀) ≤ Fintype.card (Fin a) by
      simpa only [Fintype.card_prod,Fintype.card_fin] using ha))
  let EB := Extraction.coordinateIsometry (Extraction.cardEmbedding
    (show Fintype.card (Fin J×Fin b₀) ≤ Fintype.card (Fin b) by
      simpa only [Fintype.card_prod,Fintype.card_fin] using hb))
  have hEA : EAᴴ*EA=1 := Extraction.coordinateIsometry_isometry _
  have hEB : EBᴴ*EB=1 := Extraction.coordinateIsometry_isometry _
  let T := EA ⊗ₖ EB
  have hT : Tᴴ*T=1 := Extraction.kronecker_isometry EA EB hEA hEB
  let S := fun j : Fin J => productSectorEmbedding (α := Fin a₀) (β := Fin b₀) j
  have hS (j : Fin J) : (S j)ᴴ*S j=1 := productSectorEmbedding_isometry j
  let F := fun j => T*S j*E j
  have hF (j : Fin J) : (F j)ᴴ*F j=1 :=
    Extraction.isometry_mul (T*S j) (E j) (Extraction.isometry_mul T (S j) hT (hS j)) (hE j)
  have hForth (j l : Fin J) (hjl : j≠l) : (F j)ᴴ*F l=0 := by
    have he : (F j)ᴴ*F l=(E j)ᴴ*((S j)ᴴ*S l)*E l := by
      simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Tᴴ,hT,Matrix.one_mul]
    rw [he,productSectorEmbedding_cross,if_neg hjl,Matrix.mul_zero,Matrix.zero_mul]
  obtain ⟨U,hU⟩ := exists_joint_unitary_between_orthogonal_isometries C F hC hF hCorth hForth
  let γA := Σ j : Fin J,Fin (a₀/d j)⊕Fin a₀
  let γB := Σ j : Fin J,Fin (b₀/d j)⊕Fin b₀
  let fA (j : Fin J) : (Fin (a₀/d j)⊕Fin a₀) ↪ γA :=
    ⟨fun t => ⟨j,t⟩,by intro x y h;exact eq_of_heq (Sigma.mk.inj h).2⟩
  let fB (j : Fin J) : (Fin (b₀/d j)⊕Fin b₀) ↪ γB :=
    ⟨fun t => ⟨j,t⟩,by intro x y h;exact eq_of_heq (Sigma.mk.inj h).2⟩
  let AA := fun j => extendByZero (fA j) (A j)
  let BB := fun j => extendByZero (fB j) (B j)
  have hAA (j : Fin J) : ∑ t,(AA j t)ᴴ*AA j t=1 := extendByZero_kraus_complete _ _ (hA j)
  have hBB (j : Fin J) : ∑ t,(BB j t)ᴴ*BB j t=1 := extendByZero_kraus_complete _ _ (hB j)
  let o₀ : Fin K := ⟨0,hK⟩
  let GA := Extraction.completedKraus EA (sectorKraus AA) o₀
  let GB := Extraction.completedKraus EB (sectorKraus BB) o₀
  have hGA : ∑ t,(GA t)ᴴ*GA t=1 :=
    Extraction.completedKraus_complete EA hEA _ (sectorKraus_complete AA hAA) o₀
  have hGB : ∑ t,(GB t)ᴴ*GB t=1 :=
    Extraction.completedKraus_complete EB hEB _ (sectorKraus_complete BB hBB) o₀
  have hout (j l : Fin J) (Y : Matrix (κ j) (κ l) ℂ) :
      Extraction.krausApply (Extraction.productKraus GA GB)
        ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*(C j*Y*(C l)ᴴ)*
          (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ)=
      Extraction.krausApply (Extraction.productKraus (sectorKraus AA) (sectorKraus BB))
        (S j*(E j*Y*(E l)ᴴ)*(S l)ᴴ) := by
    have henc : (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*(C j*Y*(C l)ᴴ)*
          (U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ=
        T*(S j*(E j*Y*(E l)ᴴ)*(S l)ᴴ)*Tᴴ := by
      calc
        _ = ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*C j)*Y*
          ((U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)*C l)ᴴ := by
            simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _ = _ := by rw [hU j,hU l];simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [henc]
    exact Extraction.productCompletedKraus_encoded EA EB hEA hEB
      (sectorKraus AA) (sectorKraus BB) o₀ o₀ _
  refine ⟨U,GA,GB,hGA,hGB,?_,?_⟩
  · intro j Y hY
    rw [hout,productSectorKraus_encoded]
    simp only [ite_true]
    rw [productKraus_extendByZero]
    exact hdecode j Y hY
  · intro j l hjl Y
    rw [hout,productSectorKraus_encoded]
    simp only [hjl,ite_false]

end SpectralProtocol