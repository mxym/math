import Extraction.FiniteFidelity

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ai bi ao bo κ η : Type*}
  [Fintype ai] [Fintype bi] [Fintype ao] [Fintype bo]
  [Fintype κ] [Fintype η]
  [DecidableEq ai] [DecidableEq bi] [DecidableEq ao] [DecidableEq bo]

/-- The Kraus operator on Alice's side after partial-transpose conjugation. -/
def conjugateMatrix (B : Matrix bo bi ℂ) : Matrix bo bi ℂ :=
  fun i j => star (B i j)

/-- Exact matrix-entry identity, valid on every complex input, not only states. -/
theorem product_congruence_partialTranspose
    (A : Matrix ao ai ℂ) (B : Matrix bo bi ℂ)
    (X : Matrix (ai × bi) (ai × bi) ℂ) :
    APPT.Quantum.partialTranspose
      ((A ⊗ₖ B) * APPT.Quantum.partialTranspose X * (A ⊗ₖ B)ᴴ) =
    (conjugateMatrix A ⊗ₖ B) * X * (conjugateMatrix A ⊗ₖ B)ᴴ := by
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [APPT.Quantum.partialTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, conjugateMatrix, star_mul, star_star,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext y
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A local product channel's transpose conjugate is itself an actual Kraus map. -/
theorem product_kraus_partialTranspose
    (A : κ → Matrix ao ai ℂ) (B : η → Matrix bo bi ℂ)
    (X : Matrix (ai × bi) (ai × bi) ℂ) :
    APPT.Quantum.partialTranspose
      (Extraction.krausApply (Extraction.productKraus A B)
        (APPT.Quantum.partialTranspose X)) =
    Extraction.krausApply
      (Extraction.productKraus (fun j => conjugateMatrix (A j)) B) X := by
  ext p q
  simp only [Extraction.krausApply, Extraction.productKraus,
    Matrix.sum_apply, APPT.Quantum.partialTranspose]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (congrFun (product_congruence_partialTranspose (A j.1) (B j.2) X) p) q

/-- Every physical product Kraus map has positive transpose conjugate.
Completeness is deliberately unnecessary for this positivity assertion. -/
theorem productKraus_PTConjugatePositive {d : Type*} [Fintype d] [DecidableEq d]
    (A : κ → Matrix d ai ℂ) (B : η → Matrix d bi ℂ) :
    Extraction.PTConjugatePositive (Extraction.productKraus A B) := by
  intro X hX
  rw [product_kraus_partialTranspose]
  exact Extraction.krausApply_posSemidef _ X hX

end SpectralProtocol