import SpectralProtocol.SpectralPacking

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A finite rank budget internally constructs an actual target code isometry
and complete local decoding channels. No Bell overlap or decoder correctness
premise is passed in by the caller. -/
theorem exists_packed_isometry_decoder (a b d K : ℕ) (hd : 0 < d) (hdk : d ≤ K)
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (hr : Fintype.card κ ≤ (a/d)*(b/d)) :
    ∃ (E : Matrix (Fin a × Fin b) κ ℂ)
      (A : Fin (a/d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      Eᴴ*E=1 ∧ (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      ∀ Y : Matrix κ κ ℂ,Y.PosSemidef →
        ((d:ℝ)/K)*Y.trace.re ≤
          (Extraction.bellProjector (d := Fin K)*
            Extraction.krausApply (Extraction.productKraus A B) (E*Y*Eᴴ)).trace.re := by
  classical
  have hdim : Fintype.card κ ≤ Fintype.card (Fin a × Fin b) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact hr.trans (Nat.mul_le_mul (Nat.div_le_self a d) (Nat.div_le_self b d))
  let C := Extraction.coordinateIsometry (Extraction.cardEmbedding hdim)
  have hC : Cᴴ*C=1 := Extraction.coordinateIsometry_isometry _
  let P := C*Cᴴ
  have hP : P.IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian
  have hPP : P*P=P := by
    change C*Cᴴ*(C*Cᴴ)=C*Cᴴ
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cᴴ,hC,Matrix.one_mul]
  have hrP : P.rank ≤ (a/d)*(b/d) :=
    ((Matrix.rank_mul_le_left C Cᴴ).trans (Matrix.rank_le_card_width C)).trans hr
  obtain ⟨U,A,B,hA,hB,he⟩ := finite_projection_positive_submatrix_lower a b d K hd hdk P hP hPP hrP
  let E := (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)*C
  have hU : (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hE : Eᴴ*E=1 := Extraction.isometry_mul _ _ hU hC
  refine ⟨E,A,B,hE,hA,hB,?_⟩
  intro Y hY
  let S := C*Y*Cᴴ
  have hS : S.PosSemidef := hY.mul_mul_conjTranspose_same C
  have hPS : P*S*P=S := by
    simp only [P,S,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cᴴ C,hC,Matrix.one_mul,
      ← Matrix.mul_assoc Cᴴ C,hC,Matrix.one_mul]
  have hb := he S S hS (by simpa using (Matrix.PosSemidef.zero : (0:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ).PosSemidef)) hPS
  have htrace : S.trace=Y.trace := Extraction.isometry_trace_congruence C hC Y
  have henc : (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)*S*
      (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ=E*Y*Eᴴ := by
    simp only [S,E,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rwa [htrace,henc] at hb

end SpectralProtocol