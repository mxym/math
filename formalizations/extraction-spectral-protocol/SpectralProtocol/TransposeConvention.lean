import SpectralProtocol.ProductPPT

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d]

/-- Partial transpose on the second tensor factor, used in the manuscript. -/
def secondPartialTranspose (X : Matrix (a × b) (a × b) ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  fun i j => X (i.1, j.2) (j.1, i.2)

/-- The two conventions differ by the full ordinary matrix transpose. -/
theorem secondPartialTranspose_eq_transpose_first
    (X : Matrix (a × b) (a × b) ℂ) :
    secondPartialTranspose X = (APPT.Quantum.partialTranspose X)ᵀ := rfl

theorem firstPartialTranspose_transpose
    (X : Matrix (a × b) (a × b) ℂ) :
    APPT.Quantum.partialTranspose Xᵀ = secondPartialTranspose X := rfl

theorem secondPartialTranspose_transpose
    (X : Matrix (a × b) (a × b) ℂ) :
    secondPartialTranspose Xᵀ = APPT.Quantum.partialTranspose X := rfl

/-- Base-level positivity of the transpose conjugate in the second-factor convention. -/
def SecondPTConjugatePositive
    (A : κ → Matrix (d × d) (a × b) ℂ) : Prop :=
  ∀ X : Matrix (a × b) (a × b) ℂ, X.PosSemidef →
    (secondPartialTranspose (Extraction.krausApply A (secondPartialTranspose X))).PosSemidef

/-- Actual positivity is independent of which tensor factor is transposed.
The proof uses ordinary transpose positivity on both the input and output;
no identification of two different channel maps is assumed. -/
theorem PTConjugatePositive_iff_second
    (A : κ → Matrix (d × d) (a × b) ℂ) :
    Extraction.PTConjugatePositive A ↔ SecondPTConjugatePositive A := by
  constructor
  · intro h X hX
    have h' := (h Xᵀ hX.transpose).transpose
    exact h'
  · intro h X hX
    have h' := (h Xᵀ hX.transpose).transpose
    exact h'

/-- A product channel obeys the manuscript convention as well. -/
theorem productKraus_secondPTConjugatePositive {η : Type*} [Fintype η]
    (A : κ → Matrix d a ℂ) (B : η → Matrix d b ℂ) :
    SecondPTConjugatePositive (Extraction.productKraus A B) :=
  (PTConjugatePositive_iff_second _).mp (productKraus_PTConjugatePositive A B)

end SpectralProtocol