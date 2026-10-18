import OperationalCompletion.TaggedCodes
import MinimaxProfile.Protocol

open scoped BigOperators ComplexOrder Kronecker
open Matrix SpectralProtocol MinimaxProfile
namespace OperationalCompletion
noncomputable section

variable {J α β γ δ : Type*} {κ : J → Type*}
  [Fintype J] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq J] [DecidableEq α] [DecidableEq β]
  [∀ j,Fintype (κ j)] [∀ j,DecidableEq (κ j)]

/-- Transfer a complete finite target-code family into one original-space
unitary. This construction retains both complete local Kraus witnesses. -/
theorem original_space_code_family (a b K : ℕ) (hK : 0<K)
    (C : ∀ j,Matrix (Fin a×Fin b) (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1) (hCorth : ∀ j l,j≠l → (C j)ᴴ*C l=0)
    (G : ∀ j,Matrix (α×β) (κ j) ℂ)
    (hG : ∀ j,(G j)ᴴ*G j=1) (hGorth : ∀ j l,j≠l → (G j)ᴴ*G l=0)
    (EA : Matrix (Fin a) α ℂ) (EB : Matrix (Fin b) β ℂ)
    (hEA : EAᴴ*EA=1) (hEB : EBᴴ*EB=1)
    (A : γ → Matrix (Fin K) α ℂ) (B : δ → Matrix (Fin K) β ℂ)
    (hA : ∑ t,(A t)ᴴ*A t=1) (hB : ∑ t,(B t)ᴴ*B t=1) (w : J → ℝ)
    (hdecode : ∀ j (Y : Matrix (κ j) (κ j) ℂ),Y.PosSemidef →
      w j*Y.trace.re≤(Extraction.bellProjector (d:=Fin K)*
        Extraction.krausApply (Extraction.productKraus A B) (G j*Y*(G j)ᴴ)).trace.re)
    (hoff : ∀ j l,j≠l → ∀ Y : Matrix (κ j) (κ l) ℂ,
      Extraction.krausApply (Extraction.productKraus A B) (G j*Y*(G l)ᴴ)=0) :
    ∃ V : KrausPPTProtocol a b K,V.IsProductLocal ∧
      ∀ X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ,X.PosSemidef →
        (∑ j,C j*(C j)ᴴ)*X=X*(∑ j,C j*(C j)ᴴ) →
        (∑ j,w j*((C j*(C j)ᴴ)*X).trace.re)≤V.fidelity X := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let T := EA ⊗ₖ EB
  have hT : Tᴴ*T=1 := Extraction.kronecker_isometry EA EB hEA hEB
  let F := fun j => T*G j
  have hF (j : J) : (F j)ᴴ*F j=1 := Extraction.isometry_mul _ _ hT (hG j)
  have hForth (j l : J) (hjl : j≠l) : (F j)ᴴ*F l=0 := by
    calc
      _ = (G j)ᴴ*(Tᴴ*T)*G l := by simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 0 := by rw [hT,Matrix.mul_one,hGorth j l hjl]
  obtain ⟨U,hU⟩ := exists_joint_unitary_between_orthogonal_isometries C F hC hF hCorth hForth
  let o₀ : Fin K := ⟨0,hK⟩
  let GA := Extraction.completedKraus EA A o₀
  let GB := Extraction.completedKraus EB B o₀
  have hGA := Extraction.completedKraus_complete EA hEA A hA o₀
  have hGB := Extraction.completedKraus_complete EB hEB B hB o₀
  have hout (j l : J) (Y : Matrix (κ j) (κ l) ℂ) :
      Extraction.krausApply (Extraction.productKraus GA GB)
        ((U:Matrix _ _ ℂ)*(C j*Y*(C l)ᴴ)*(U:Matrix _ _ ℂ)ᴴ)=
      Extraction.krausApply (Extraction.productKraus A B) (G j*Y*(G l)ᴴ) := by
    have he : (U:Matrix _ _ ℂ)*(C j*Y*(C l)ᴴ)*(U:Matrix _ _ ℂ)ᴴ=
        T*(G j*Y*(G l)ᴴ)*Tᴴ := by
      calc
        _ = ((U:Matrix _ _ ℂ)*C j)*Y*((U:Matrix _ _ ℂ)*C l)ᴴ := by
          simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _ = _ := by rw [hU j,hU l]; simp only [F,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he]
    exact Extraction.productCompletedKraus_encoded EA EB hEA hEB A B o₀ o₀ _
  let Q := physicalChannelLinearMap (Extraction.productKraus GA GB) U
  have hQ (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hX : X.PosSemidef) :
      (Q X).PosSemidef := physicalChannelLinearMap_posSemidef _ _ _ hX
  have hdec (j : J) (Y : Matrix (κ j) (κ j) ℂ) (hY : Y.PosSemidef) :
      w j*Y.trace.re≤(Extraction.bellProjector (d:=Fin K)*Q (C j*Y*(C j)ᴴ)).trace.re := by
    have h := hdecode j Y hY
    rw [←hout j j Y] at h
    simpa only [Q,physicalChannelLinearMap,LinearMap.coe_mk,AddHom.coe_mk] using h
  have hzero (j l : J) (hjl : j≠l) (Y : Matrix (κ j) (κ l) ℂ) : Q (C j*Y*(C l)ᴴ)=0 := by
    have h := hoff j l hjl Y
    rw [←hout j l Y] at h
    simpa only [Q,physicalChannelLinearMap,LinearMap.coe_mk,AddHom.coe_mk] using h
  refine ⟨localProtocol U GA GB hGA hGB,localProtocol_isProductLocal U GA GB hGA hGB,?_⟩
  intro X hX hcomm
  have h := channel_weighted_block_lower Q hQ (Extraction.bellProjector (d:=Fin K))
    (Extraction.bellProjector_density (d:=Fin K)).1 C hC hCorth w hdec hzero X hX hcomm
  rw [localProtocol_fidelity]
  exact h

end
end OperationalCompletion
