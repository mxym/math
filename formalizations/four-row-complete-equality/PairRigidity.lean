import FourRowTradeoff

/-! Rigidity of the actual four-coordinate Cauchy deficit.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
AI-assisted research; no external funding. -/
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- A sum-of-squares identity for arbitrary complex coordinates. -/
theorem variance_four (z : Row) :
    4 * (∑ i, Complex.normSq (z i)) - Complex.normSq (∑ i, z i) =
      Complex.normSq (z 0-z 1) + Complex.normSq (z 0-z 2) +
      Complex.normSq (z 0-z 3) + Complex.normSq (z 1-z 2) +
      Complex.normSq (z 1-z 3) + Complex.normSq (z 2-z 3) := by
  simp [Fin.sum_univ_succ, Complex.normSq_apply]
  ring

theorem variance_four_eq_zero_iff (z : Row) :
    Complex.normSq (∑ i, z i) = 4 * (∑ i, Complex.normSq (z i)) ↔
      ∀ i, z i = z 0 := by
  constructor
  · intro h
    have hv := variance_four z
    have h01 := Complex.normSq_nonneg (z 0-z 1)
    have h02 := Complex.normSq_nonneg (z 0-z 2)
    have h03 := Complex.normSq_nonneg (z 0-z 3)
    have h12 := Complex.normSq_nonneg (z 1-z 2)
    have h13 := Complex.normSq_nonneg (z 1-z 3)
    have h23 := Complex.normSq_nonneg (z 2-z 3)
    have e01 : Complex.normSq (z 0-z 1) = 0 := by linarith
    have e02 : Complex.normSq (z 0-z 2) = 0 := by linarith
    have e03 : Complex.normSq (z 0-z 3) = 0 := by linarith
    have eq01 : z 0 = z 1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp e01)
    have eq02 : z 0 = z 2 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp e02)
    have eq03 : z 0 = z 3 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp e03)
    intro i
    fin_cases i
    · rfl
    · exact eq01.symm
    · exact eq02.symm
    · exact eq03.symm
  · intro h
    simp [h, Complex.normSq_apply]
    ring

/-- The exact equality condition in the collision Cauchy inequality. -/
theorem collision_eq_iff_products_constant (a b : Row) :
    overlap a b = 4 * collision a b ↔
      ∀ j, a j * conj (b j) = a 0 * conj (b 0) := by
  simpa only [overlap, collision, Complex.normSq_mul, Complex.normSq_conj]
    using variance_four_eq_zero_iff (fun j => a j * conj (b j))

theorem rowSq_eq_zero_iff (a : Row) :
    rowSq a = 0 ↔ ∀ j, a j = 0 := by
  simpa only [rowSq, Finset.mem_univ, forall_const, Complex.normSq_eq_zero] using
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : Fin 4) (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (a i)))

theorem rowSq_pos_iff (a : Row) :
    0 < rowSq a ↔ ∃ j, a j ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [rowSq_nonneg, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    rowSq_eq_zero_iff, not_forall]

/-- Nonzero rows are stated by their actual entries. -/
def NonzeroRows (A : Mat) : Prop := ∀ i, ∃ j, A i j ≠ 0

/-- Every pair of distinct rows has a column-independent conjugate product. -/
def ConstantRowProducts (A : Mat) : Prop :=
  ∀ i j, i ≠ j → ∀ k, A i k * conj (A j k) = A i 0 * conj (A j 0)

theorem rowProduct_pos (A : Mat) (h : NonzeroRows A) : 0 < rowProduct A := by
  apply Finset.prod_pos
  intro i _
  exact Real.sqrt_pos.mpr ((rowSq_pos_iff (A i)).mpr (h i))

theorem det_norm_le_rowProduct (A : Mat) : ‖A.det‖ ≤ rowProduct A := by
  have h1 : altEnergy (A 0) (A 1) ≤ rowSq (A 0)*rowSq (A 1) := by
    rw [altEnergy_identity]; linarith [overlap_nonneg (A 0) (A 1)]
  have h2 : altEnergy (A 2) (A 3) ≤ rowSq (A 2)*rowSq (A 3) := by
    rw [altEnergy_identity]; linarith [overlap_nonneg (A 2) (A 3)]
  have h := (det_sq_bound A).trans (mul_le_mul h1 h2
    (altEnergy_nonneg _ _) (mul_nonneg (rowSq_nonneg _) (rowSq_nonneg _)))
  have he : (rowSq (A 0)*rowSq (A 1)) * (rowSq (A 2)*rowSq (A 3)) =
      rowProduct A ^ 2 := by rw [rowProduct_sq]; ring
  rw [he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (rowProduct_nonneg A)).mp h

#print axioms collision_eq_iff_products_constant
#print axioms det_norm_le_rowProduct
end
end FourRowTradeoff
