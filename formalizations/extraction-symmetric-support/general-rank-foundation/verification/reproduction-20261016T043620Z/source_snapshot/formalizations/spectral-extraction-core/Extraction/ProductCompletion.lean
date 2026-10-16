import Extraction.KrausCompletion

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {a b α β ο π κ τ : Type*}
  [Fintype a] [Fintype b] [Fintype α] [Fintype β]
  [Fintype ο] [Fintype π] [Fintype κ] [Fintype τ]
  [DecidableEq a] [DecidableEq b] [DecidableEq α] [DecidableEq β]
  [DecidableEq ο] [DecidableEq π]

def productKraus (A : κ → Matrix ο a ℂ) (B : τ → Matrix π b ℂ) :
    κ × τ → Matrix (ο × π) (a × b) ℂ :=
  fun j => A j.1 ⊗ₖ B j.2

theorem productKraus_complete
    (A : κ → Matrix ο a ℂ) (B : τ → Matrix π b ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    (∑ j, (productKraus A B j)ᴴ * productKraus A B j) = 1 := by
  have h (j : κ) (l : τ) :
      (productKraus A B (j,l))ᴴ * productKraus A B (j,l) =
      ((A j)ᴴ * A j) ⊗ₖ ((B l)ᴴ * B l) := by
    simp only [productKraus, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, h]
  have hs : (∑ j, ∑ l, ((A j)ᴴ * A j) ⊗ₖ ((B l)ᴴ * B l)) =
      (∑ j, (A j)ᴴ * A j) ⊗ₖ (∑ l, (B l)ᴴ * B l) := by
    ext p q
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs, hA, hB, Matrix.one_kronecker_one]

/-- Product isometries remain isometries on the actual product system. -/
theorem kronecker_isometry (E : Matrix a α ℂ) (F : Matrix b β ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    (E ⊗ₖ F)ᴴ * (E ⊗ₖ F) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hE, hF,
    Matrix.one_kronecker_one]

/-- Completing each party separately preserves the exact product protocol on
the original good product subspace; all three kinds of leftover branches vanish. -/
theorem productCompletedKraus_encoded
    (E : Matrix a α ℂ) (F : Matrix b β ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (A : κ → Matrix ο α ℂ) (B : τ → Matrix π β ℂ)
    (o₀ : ο) (p₀ : π) (X : Matrix (α × β) (α × β) ℂ) :
    krausApply (productKraus (completedKraus E A o₀) (completedKraus F B p₀))
      ((E ⊗ₖ F) * X * (E ⊗ₖ F)ᴴ) =
    krausApply (productKraus A B) X := by
  have hb (j : (κ ⊕ a) × (τ ⊕ b)) :
      productKraus (completedKraus E A o₀) (completedKraus F B p₀) j *
        ((E ⊗ₖ F) * X * (E ⊗ₖ F)ᴴ) *
        (productKraus (completedKraus E A o₀) (completedKraus F B p₀) j)ᴴ =
      ((completedKraus E A o₀ j.1 * E) ⊗ₖ (completedKraus F B p₀ j.2 * F)) * X *
      ((completedKraus E A o₀ j.1 * E) ⊗ₖ (completedKraus F B p₀ j.2 * F))ᴴ := by
    simp only [Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul, productKraus,
      Matrix.mul_assoc]
  unfold krausApply
  simp_rw [hb]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type,
    completedKraus_inl_mul E hE, completedKraus_inl_mul F hF,
    completedKraus_inr_mul E hE, completedKraus_inr_mul F hF,
    Matrix.zero_kronecker, Matrix.kronecker_zero, Matrix.zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, productKraus]

end Extraction
