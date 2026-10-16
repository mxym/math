import Extraction.ProductCompletion

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq η]

/-- The actual coordinate matrix of a finite injection. -/
def coordinateIsometry (f : κ ↪ ι) : Matrix ι κ ℂ :=
  fun p q => if p = f q then 1 else 0

theorem coordinateIsometry_isometry (f : κ ↪ ι) :
    (coordinateIsometry f)ᴴ * coordinateIsometry f = 1 := by
  ext p q
  by_cases hpq : p = q <;>
    simp_all [coordinateIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, apply_ite, ite_mul, mul_ite, eq_comm]

/-- The packing label injection is constructed from the actual finite cardinals. -/
noncomputable def cardEmbedding (h : Fintype.card κ ≤ Fintype.card ι) : κ ↪ ι where
  toFun := fun i => (Fintype.equivFin ι).symm
    ⟨((Fintype.equivFin κ) i).val, lt_of_lt_of_le ((Fintype.equivFin κ) i).isLt h⟩
  inj' := by
    intro i j hij
    apply (Fintype.equivFin κ).injective
    apply Fin.ext
    have hh := congrArg (fun x : ι => ((Fintype.equivFin ι) x).val) hij
    simpa using hh

theorem isometry_trace_congruence (E : Matrix ι κ ℂ) (hE : Eᴴ * E = 1)
    (X : Matrix κ κ ℂ) : (E * X * Eᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hE, Matrix.one_mul]

theorem isometry_mul (E : Matrix ι η ℂ) (F : Matrix η κ ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    (E * F)ᴴ * (E * F) = 1 := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, hF]

variable {a b d u v : Type*}
  [Fintype a] [Fintype b] [Fintype d] [Fintype u] [Fintype v]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [DecidableEq u] [DecidableEq v]
  [Nonempty d]

/-- A finite-dimensional common-subspace extractor.
Its unitary and both complete local Kraus families are fixed before the input
matrix. The proof includes arbitrary input remainders and coherent logical states. -/
theorem exists_common_subspace_exact_extractor
    (C : Matrix (a × b) κ ℂ) (hC : Cᴴ * C = 1)
    (EA : Matrix a (d × u) ℂ) (EB : Matrix b (d × v) ℂ)
    (hEA : EAᴴ * EA = 1) (hEB : EBᴴ * EB = 1)
    (hr : Fintype.card κ ≤ Fintype.card (u × v)) :
    ∃ (U : Matrix.unitaryGroup (a × b) ℂ)
      (A : u ⊕ a → Matrix d a ℂ) (B : v ⊕ b → Matrix d b ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ∀ X : Matrix (a × b) (a × b) ℂ,
        (C * Cᴴ) * X * (C * Cᴴ) = X →
        krausApply (productKraus A B)
          ((U : Matrix (a × b) (a × b) ℂ) * X *
            (U : Matrix (a × b) (a × b) ℂ)ᴴ) =
        X.trace • bellProjector (d := d) := by
  let T := EA ⊗ₖ EB
  let V := codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d)
  let G := coordinateIsometry (cardEmbedding hr)
  have hT : Tᴴ * T = 1 := kronecker_isometry EA EB hEA hEB
  have hV : Vᴴ * V = 1 := codeEmbedding_isometry
  have hG : Gᴴ * G = 1 := coordinateIsometry_isometry _
  have hE : (T * V * G)ᴴ * (T * V * G) = 1 :=
    isometry_mul (T * V) G (isometry_mul T V hT hV) hG
  obtain ⟨U, hU⟩ := exists_unitary_between_isometries C (T * V * G) hC hE
  let o₀ := Classical.arbitrary d
  let A := completedKraus EA (eraseKraus (d := d) (u := u)) o₀
  let B := completedKraus EB (eraseKraus (d := d) (u := v)) o₀
  refine ⟨U, A, B,
    completedKraus_complete EA hEA _ eraseKraus_complete o₀,
    completedKraus_complete EB hEB _ eraseKraus_complete o₀, ?_⟩
  intro X hX
  let Y := Cᴴ * X * C
  have hXY : C * Y * Cᴴ = X := by
    simpa only [Y, Matrix.mul_assoc] using hX
  have hUY : (U : Matrix (a × b) (a × b) ℂ) * X *
      (U : Matrix (a × b) (a × b) ℂ)ᴴ =
      T * (V * (G * Y * Gᴴ) * Vᴴ) * Tᴴ := by
    rw [← hXY]
    have hh : (U : Matrix (a × b) (a × b) ℂ) * (C * Y * Cᴴ) *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ =
        ((U : Matrix (a × b) (a × b) ℂ) * C) * Y *
          ((U : Matrix (a × b) (a × b) ℂ) * C)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hh, hU]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hUY]
  change krausApply
    (productKraus (completedKraus EA _ o₀) (completedKraus EB _ o₀))
      ((EA ⊗ₖ EB) * (V * (G * Y * Gᴴ) * Vᴴ) * (EA ⊗ₖ EB)ᴴ) =
    X.trace • bellProjector
  rw [productCompletedKraus_encoded EA EB hEA hEB]
  change krausApply (productEraseKraus (d := d))
      (V * (G * Y * Gᴴ) * Vᴴ) = X.trace • bellProjector
  rw [productEraseKraus_encoded, isometry_trace_congruence G hG]
  have htrace : Y.trace = X.trace := by
    rw [← hXY, isometry_trace_congruence C hC]
  rw [htrace]
  rfl

end Extraction
