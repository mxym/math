import OperationalCompletion.CodeFamily

open scoped BigOperators ComplexOrder Kronecker
open Matrix SpectralProtocol MinimaxProfile
namespace OperationalCompletion
noncomputable section

/-- One large local sector and finitely many small sectors admit one original
unitary and one complete pair of local decoders. Only literal projection ranks
and integer packing budgets appear in the hypotheses. -/
theorem heterogeneous_projection_protocol (a b A B a₀ b₀ K J d₀ : ℕ) (hK : 0<K)
    (hd₀ : 0<d₀) (hd₀K : d₀≤K) (d : Fin J → ℕ) (hd : ∀ j,0<d j) (hdk : ∀ j,d j≤K)
    (ha : A+J*a₀≤a) (hb : B+J*b₀≤b)
    (P : Option (Fin J) → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hP : ∀ j,(P j).IsHermitian) (hPP : ∀ j,P j*P j=P j)
    (horth : ∀ j l,j≠l → P j*P l=0)
    (hr₀ : (P none).rank≤(A/d₀)*(B/d₀))
    (hr : ∀ j,(P (some j)).rank≤(a₀/d j)*(b₀/d j)) :
    ∃ V : KrausPPTProtocol a b K,V.IsProductLocal ∧
      ∀ X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ,X.PosSemidef →
        (∑ j,P j)*X=X*(∑ j,P j) →
        ((d₀:ℝ)/K)*(P none*X).trace.re+
          (∑ j : Fin J,((d j:ℝ)/K)*(P (some j)*X).trace.re)≤V.fidelity X := by
  classical
  choose κ iκ eκ C hC hCP hcard using
    fun j => Extraction.exists_projection_factor (P j) (hP j) (hPP j)
  letI : ∀ j,Fintype (κ j) := iκ
  letI : ∀ j,DecidableEq (κ j) := eκ
  have hCorth := projection_factors_orthogonal P C hC hCP horth
  obtain ⟨E₀,A₀,B₀,hE₀,hA₀,hB₀,hdec₀⟩ := exists_packed_isometry_decoder A B d₀ K hd₀ hd₀K
    (κ none) (by rw [hcard]; exact hr₀)
  obtain ⟨Fm,Am,Bm,hFm,hFmorth,hAm,hBm,hdecm,hoffm⟩ :=
    exists_tagged_packed_codes a₀ b₀ K J hK d hd hdk (fun j => κ (some j))
      (fun j => by rw [hcard]; exact hr j)
  let α := Fin A⊕(Fin J×Fin a₀)
  let β := Fin B⊕(Fin J×Fin b₀)
  let L : Matrix (α×β) (Fin A×Fin B) ℂ := bipartiteLeft
  let R : Matrix (α×β) ((Fin J×Fin a₀)×(Fin J×Fin b₀)) ℂ := bipartiteRight
  have hL : Lᴴ*L=1 := bipartiteLeft_isometry
  have hR : Rᴴ*R=1 := bipartiteRight_isometry
  have hLR : Lᴴ*R=0 := bipartiteLeft_right_cross
  have hRL : Rᴴ*L=0 := bipartiteRight_left_cross
  let G : ∀ j : Option (Fin J),Matrix (α×β) (κ j) ℂ :=
    fun j => match j with | none => L*E₀ | some j => R*Fm j
  have hG (j : Option (Fin J)) : (G j)ᴴ*G j=1 := by
    cases j with
    | none => exact Extraction.isometry_mul L E₀ hL hE₀
    | some j => exact Extraction.isometry_mul R (Fm j) hR (hFm j)
  have hGorth (j l : Option (Fin J)) (hjl : j≠l) : (G j)ᴴ*G l=0 := by
    cases j with
    | none =>
      cases l with
      | none => exact False.elim (hjl rfl)
      | some l =>
        calc
          _ = E₀ᴴ*(Lᴴ*R)*Fm l := by simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
          _ = 0 := by rw [hLR,Matrix.mul_zero,Matrix.zero_mul]
    | some j =>
      cases l with
      | none =>
        calc
          _ = (Fm j)ᴴ*(Rᴴ*L)*E₀ := by simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
          _ = 0 := by rw [hRL,Matrix.mul_zero,Matrix.zero_mul]
      | some l =>
        calc
          _ = (Fm j)ᴴ*(Rᴴ*R)*Fm l := by simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
          _ = 0 := by rw [hR,Matrix.mul_one,hFmorth j l (fun h => hjl (congrArg some h))]
  let Aj := joinedKraus A₀ Am
  let Bj := joinedKraus B₀ Bm
  have hAj := joinedKraus_complete A₀ Am hA₀ hAm
  have hBj := joinedKraus_complete B₀ Bm hB₀ hBm
  let w : Option (Fin J) → ℝ := fun j => j.elim ((d₀:ℝ)/(K:ℝ)) (fun j => (d j:ℝ)/(K:ℝ))
  have hdec (j : Option (Fin J)) (Y : Matrix (κ j) (κ j) ℂ) (hY : Y.PosSemidef) :
      w j*Y.trace.re≤(Extraction.bellProjector (d:=Fin K)*
        Extraction.krausApply (Extraction.productKraus Aj Bj) (G j*Y*(G j)ᴴ)).trace.re := by
    cases j with
    | none =>
      have he : G none*Y*(G none)ᴴ=L*(E₀*Y*E₀ᴴ)*Lᴴ := by
        simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [he,productJoinedKraus_left]
      exact hdec₀ Y hY
    | some j =>
      have he : G (some j)*Y*(G (some j))ᴴ=R*(Fm j*Y*(Fm j)ᴴ)*Rᴴ := by
        simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [he,productJoinedKraus_right]
      exact hdecm j Y hY
  have hoff (j l : Option (Fin J)) (hjl : j≠l) (Y : Matrix (κ j) (κ l) ℂ) :
      Extraction.krausApply (Extraction.productKraus Aj Bj) (G j*Y*(G l)ᴴ)=0 := by
    cases j with
    | none =>
      cases l with
      | none => exact False.elim (hjl rfl)
      | some l =>
        have he : G none*Y*(G (some l))ᴴ=L*(E₀*Y*(Fm l)ᴴ)*Rᴴ := by
          simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
        rw [he,productJoinedKraus_left_right]
    | some j =>
      cases l with
      | none =>
        have he : G (some j)*Y*(G none)ᴴ=R*(Fm j*Y*E₀ᴴ)*Lᴴ := by
          simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
        rw [he,productJoinedKraus_right_left]
      | some l =>
        have he : G (some j)*Y*(G (some l))ᴴ=R*(Fm j*Y*(Fm l)ᴴ)*Rᴴ := by
          simp only [G,Matrix.conjTranspose_mul,Matrix.mul_assoc]
        rw [he,productJoinedKraus_right]
        exact hoffm j l (fun h => hjl (congrArg some h)) Y
  let EA := Extraction.coordinateIsometry (Extraction.cardEmbedding
    (show Fintype.card α≤Fintype.card (Fin a) by
      simpa only [α,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using ha))
  let EB := Extraction.coordinateIsometry (Extraction.cardEmbedding
    (show Fintype.card β≤Fintype.card (Fin b) by
      simpa only [β,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hb))
  obtain ⟨V,hLocal,hV⟩ := original_space_code_family a b K hK C hC hCorth G hG hGorth EA EB
    (Extraction.coordinateIsometry_isometry _) (Extraction.coordinateIsometry_isometry _)
    Aj Bj hAj hBj w hdec hoff
  refine ⟨V,hLocal,?_⟩
  intro X hX hcomm
  have hc : (∑ j,C j*(C j)ᴴ)*X=X*(∑ j,C j*(C j)ᴴ) := by simpa only [hCP] using hcomm
  have h := hV X hX hc
  simpa only [hCP,Fintype.sum_option,w,Option.elim_none,Option.elim_some] using h

end
end OperationalCompletion
