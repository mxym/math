import Mxym
open scoped BigOperators Classical
open Mxym.Rademacher Mxym.Determinant
namespace NormedAudit
noncomputable section

private theorem cons_two {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 2) → α) :
    Fin.cons (α := fun _ : Fin (n + 3) => α) a f 2 = f 1 := rfl
private theorem cons_three {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 3) → α) :
    Fin.cons (α := fun _ : Fin (n + 4) => α) a f 3 = f 2 := rfl

def paddedC : Fin 3 → ℝ := ![1, 1, 0]
def paddedX : Fin 3 → ℝ := ![1, -1, 42]
theorem padded_relation : ∑ j, paddedC j • paddedX j = 0 := by
  norm_num [paddedC, paddedX, Fin.sum_univ_succ, smul_eq_mul, cons_two]
theorem padded_unit : ∀ j, paddedC j ≠ 0 → ‖paddedX j‖ = 1 := by
  intro j hj
  fin_cases j <;> norm_num [paddedC, paddedX, cons_two, Real.norm_eq_abs] at *
example : ∀ i, |paddedC i| ≤ (∑ j, |paddedC j|)/2 :=
  Mxym.NormedBalance.coefficient_balance _ _ padded_relation padded_unit
example : mean paddedC = (∑ j, |paddedC j|)/2 := by
  apply (Mxym.NormedBalance.rademacher_equality_iff _ _ padded_relation padded_unit).2
  right
  exact ⟨0, by norm_num [paddedC, Fin.sum_univ_succ, cons_two]⟩
example : ‖paddedX 2‖ = 42 := by norm_num [paddedX, cons_two, Real.norm_eq_abs]

example (x : Fin 3 → ℝ) : mean (fun _ : Fin 3 => (0 : ℝ)) ≤ 0 := by
  simpa using Mxym.NormedBalance.rademacher_bound (fun _ : Fin 3 => (0 : ℝ)) x
    (by simp) (by intro j hj; exact False.elim (hj rfl))
example : mean (fun _ : Fin 0 => (0 : ℝ)) ≤ 0 := by
  simpa using Mxym.NormedBalance.rademacher_bound (fun _ : Fin 0 => (0 : ℝ))
    (fun _ : Fin 0 => (5 : ℝ)) (by simp) (by intro j; exact Fin.elim0 j)

def fourC : Fin 4 → ℝ := fun _ => 1
def fourX : Fin 4 → ℝ := ![1, -1, 1, -1]
example : (∑ j, fourC j • fourX j) = 0 ∧ (∀ j, fourC j ≠ 0 → ‖fourX j‖ = 1) := by
  constructor
  · norm_num [fourC, fourX, Fin.sum_univ_succ, smul_eq_mul, cons_two, cons_three]
  · intro j hj; fin_cases j <;> norm_num [fourX, cons_two, cons_three, Real.norm_eq_abs]
theorem four_mean : mean fourC = 3/2 := by
  norm_num [fourC, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, Fin.default_eq_zero]
example : mean fourC < (∑ j, |fourC j|)/2 := by norm_num [four_mean, fourC]

def oneC : Fin 1 → ℝ := fun _ => 1
def missingUnitX : Fin 1 → ℝ := fun _ => 0
def missingRelationX : Fin 1 → ℝ := fun _ => 1
example : (∑ j, oneC j • missingUnitX j) = 0 ∧ ‖missingUnitX 0‖ ≠ 1 := by
  norm_num [oneC, missingUnitX]
example : (∀ j, oneC j ≠ 0 → ‖missingRelationX j‖ = 1) ∧
    (∑ j, oneC j • missingRelationX j) ≠ 0 := by
  norm_num [oneC, missingRelationX]
theorem refute_missing_unit : ¬ (|oneC 0| ≤ (∑ j, |oneC j|)/2) := by norm_num [oneC]
theorem refute_missing_relation : ¬ (|oneC 0| ≤ (∑ j, |oneC j|)/2) := refute_missing_unit

def smallNormC : Fin 2 → ℝ := ![2, 1]
def smallNormX : Fin 2 → ℝ := ![1/2, -1]
example : (∑ j, smallNormC j • smallNormX j) = 0 ∧ (∀ j, ‖smallNormX j‖ ≤ 1) := by
  constructor
  · norm_num [smallNormC, smallNormX, Fin.sum_univ_succ, smul_eq_mul]
  · intro j; fin_cases j <;> norm_num [smallNormX, Real.norm_eq_abs]
theorem refute_norm_le_one : ¬ (|smallNormC 0| ≤ (∑ j, |smallNormC j|)/2) := by
  norm_num [smallNormC, Fin.sum_univ_succ]

def evalOne : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ
def unitMatrix : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]
def nonunitMatrix : Matrix (Fin 1) (Fin 2) ℝ := !![2, -1]
theorem unitMatrix_unit : ∀ j, cofactor unitMatrix j ≠ 0 → ‖evalOne (column unitMatrix j)‖ = 1 := by
  intro j hj
  fin_cases j <;> norm_num [evalOne, LinearEquiv.funUnique, column, unitMatrix, Real.norm_eq_abs]
example : ∀ i, |cofactor unitMatrix i| ≤ (∑ j, |cofactor unitMatrix j|)/2 :=
  cofactor_balance_of_normalized_columns _ evalOne unitMatrix_unit
example : mean (cofactor unitMatrix) = (∑ j, |cofactor unitMatrix j|)/2 := by
  have h := normalized_sign_average_equality_iff unitMatrix evalOne unitMatrix_unit
  rw [sign_average_eq] at h
  apply h.2
  left
  have bound := Fintype.card_subtype_le (fun j : Fin 2 => cofactor unitMatrix j ≠ 0)
  norm_num at bound ⊢
  omega

theorem nonunit_cofactor_zero : cofactor nonunitMatrix 0 = -1 := by
  norm_num [cofactor, nonunitMatrix, Matrix.det_fin_one, Matrix.submatrix]
theorem nonunit_cofactor_one : cofactor nonunitMatrix 1 = -2 := by
  norm_num [cofactor, nonunitMatrix, Matrix.det_fin_one, Matrix.submatrix]
example : (∑ j, cofactor nonunitMatrix j • column nonunitMatrix j) = 0 :=
  cofactor_vector_relation _
example : ‖evalOne (column nonunitMatrix 0)‖ = 2 := by
  norm_num [evalOne, LinearEquiv.funUnique, column, nonunitMatrix, Real.norm_eq_abs]
theorem refute_nonunit_columns : ¬ (|cofactor nonunitMatrix 1| ≤ (∑ j, |cofactor nonunitMatrix j|)/2) := by
  norm_num [Fin.sum_univ_succ, nonunit_cofactor_zero, nonunit_cofactor_one]
theorem nonunit_cofactor_mean : mean (cofactor nonunitMatrix) = 2 := by
  norm_num [mean, signedSum, sum_signs_succ, Fin.sum_univ_succ, sign,
    cofactor, nonunitMatrix, Matrix.det_fin_one, Matrix.submatrix, Fin.default_eq_zero]
example : ¬ ((∑ ε : Fin 2 → Bool,
    |(lift (fun i j => sign (ε j) * nonunitMatrix i j) (fun _ => 1)).det|) /
      Fintype.card (Fin 2 → Bool) ≤ (∑ j, |cofactor nonunitMatrix j|)/2) := by
  rw [sign_average_eq, nonunit_cofactor_mean]
  norm_num [Fin.sum_univ_succ, nonunit_cofactor_zero, nonunit_cofactor_one]

example : ∀ i, |cofactor (0 : Matrix (Fin 2) (Fin 3) ℝ) i| ≤
    (∑ j, |cofactor (0 : Matrix (Fin 2) (Fin 3) ℝ) j|)/2 := by
  apply cofactor_balance_of_normalized_columns _ (LinearEquiv.refl ℝ (Fin 2 → ℝ))
  intro j hj
  exfalso
  apply hj
  simp [cofactor, Matrix.submatrix_zero]

-- In dimension zero the sole empty minor is one, but the sole column has norm zero.
-- The normalized cofactor hypotheses are therefore impossible in this boundary case.
example (hunit : ∀ j, cofactor (0 : Matrix (Fin 0) (Fin 1) ℝ) j ≠ 0 →
    ‖(LinearEquiv.refl ℝ (Fin 0 → ℝ)) (column (0 : Matrix (Fin 0) (Fin 1) ℝ) j)‖ = 1) : False := by
  have h := hunit 0 (by norm_num [cofactor])
  have hz : column (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 = (0 : Fin 0 → ℝ) := by
    funext i
    exact Fin.elim0 i
  norm_num [hz] at h

end
end NormedAudit
