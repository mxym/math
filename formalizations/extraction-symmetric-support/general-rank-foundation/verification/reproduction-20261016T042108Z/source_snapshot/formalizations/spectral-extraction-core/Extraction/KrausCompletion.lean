import Extraction.UnitaryExtension

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

variable {ι α ο κ : Type*} [Fintype ι] [Fintype α] [Fintype ο] [Fintype κ]
  [DecidableEq ι] [DecidableEq α] [DecidableEq ο]

/-- Send one row of the unused input component to one fixed output coordinate. -/
def residualKraus (o₀ : ο) (R : Matrix ι α ℂ) (i : ι) : Matrix ο α ℂ :=
  fun o z => if o = o₀ then R i z else 0

theorem residualKraus_complete (o₀ : ο) (R : Matrix ι α ℂ) :
    (∑ i, (residualKraus o₀ R i)ᴴ * residualKraus o₀ R i) = Rᴴ * R := by
  ext p q
  simp [residualKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite, ite_mul, mul_ite, eq_comm]

theorem residualKraus_mul {β : Type*} [Fintype β]
    (o₀ : ο) (R : Matrix ι α ℂ) (i : ι) (E : Matrix α β ℂ) :
    residualKraus o₀ R i * E = residualKraus o₀ (R * E) i := by
  ext o z
  by_cases ho : o = o₀ <;>
    simp [residualKraus, Matrix.mul_apply, ho]

/-- Complete a channel from an isometrically embedded subspace to the whole
original input. All unused components are retained as deterministic branches. -/
def completedKraus (E : Matrix ι α ℂ) (A : κ → Matrix ο α ℂ) (o₀ : ο) :
    κ ⊕ ι → Matrix ο ι ℂ
  | Sum.inl j => A j * Eᴴ
  | Sum.inr i => residualKraus o₀ (1 - E * Eᴴ) i

theorem isometry_complement_hermitian (E : Matrix ι α ℂ) :
    (1 - E * Eᴴ).IsHermitian := by
  change (1 - E * Eᴴ)ᴴ = 1 - E * Eᴴ
  simp

theorem isometry_complement_square (E : Matrix ι α ℂ) (hE : Eᴴ * E = 1) :
    (1 - E * Eᴴ) * (1 - E * Eᴴ) = 1 - E * Eᴴ := by
  have hp : E * Eᴴ * (E * Eᴴ) = E * Eᴴ := by
    calc
      _ = E * (Eᴴ * E) * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hE]; simp
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hp]
  abel

theorem completedKraus_complete (E : Matrix ι α ℂ) (hE : Eᴴ * E = 1)
    (A : κ → Matrix ο α ℂ) (hA : ∑ j, (A j)ᴴ * A j = 1) (o₀ : ο) :
    (∑ j, (completedKraus E A o₀ j)ᴴ * completedKraus E A o₀ j) = 1 := by
  have hleft : (∑ j, (A j * Eᴴ)ᴴ * (A j * Eᴴ)) = E * Eᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = E * (∑ j, (A j)ᴴ * A j) * Eᴴ := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA]; simp
  simp only [Fintype.sum_sum_type, completedKraus, hleft, residualKraus_complete]
  rw [(isometry_complement_hermitian E).eq, isometry_complement_square E hE]
  abel

theorem completedKraus_inl_mul (E : Matrix ι α ℂ) (hE : Eᴴ * E = 1)
    (A : κ → Matrix ο α ℂ) (o₀ : ο) (j : κ) :
    completedKraus E A o₀ (Sum.inl j) * E = A j := by
  simp only [completedKraus, Matrix.mul_assoc, hE, Matrix.mul_one]

theorem completedKraus_inr_mul (E : Matrix ι α ℂ) (hE : Eᴴ * E = 1)
    (A : κ → Matrix ο α ℂ) (o₀ : ο) (i : ι) :
    completedKraus E A o₀ (Sum.inr i) * E = 0 := by
  rw [completedKraus, residualKraus_mul]
  have he : (1 - E * Eᴴ) * E = 0 := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hE, Matrix.mul_one, sub_self]
  rw [he]
  ext p q
  simp [residualKraus]

/-- The completion agrees exactly with the original channel on every encoded
matrix, including all coherent off-diagonal entries. -/
theorem completedKraus_encoded (E : Matrix ι α ℂ) (hE : Eᴴ * E = 1)
    (A : κ → Matrix ο α ℂ) (o₀ : ο) (X : Matrix α α ℂ) :
    krausApply (completedKraus E A o₀) (E * X * Eᴴ) = krausApply A X := by
  have hb (j : κ ⊕ ι) :
      completedKraus E A o₀ j * (E * X * Eᴴ) * (completedKraus E A o₀ j)ᴴ =
      (completedKraus E A o₀ j * E) * X * (completedKraus E A o₀ j * E)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [krausApply, hb, Fintype.sum_sum_type,
    completedKraus_inl_mul E hE, completedKraus_inr_mul E hE,
    Matrix.zero_mul, Matrix.mul_zero, Finset.sum_const_zero, add_zero]

end Extraction
