import PairRigidity
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- Row relabeling preserves the actual product of Euclidean row norms. -/
theorem rowProduct_permute (A : Mat) (σ : Equiv.Perm (Fin 4)) :
    rowProduct (A.submatrix σ id) = rowProduct A := by
  exact Equiv.prod_comp σ (fun i => rowNorm (A i))

theorem det_norm_permute (A : Mat) (σ : Equiv.Perm (Fin 4)) :
    ‖(A.submatrix σ id).det‖ = ‖A.det‖ := by
  rw [Matrix.det_permute, norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- The permutation placing a prescribed distinct row pair first. -/
def pairPerm (i j : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 i).trans (Equiv.swap ((Equiv.swap 0 i) 1) j)

theorem pairPerm_zero (i j : Fin 4) (h : i ≠ j) : pairPerm i j 0 = i := by
  fin_cases i <;> fin_cases j <;>
    simp_all [pairPerm, Equiv.trans_apply, Equiv.swap_apply_def]

theorem pairPerm_one (i j : Fin 4) : pairPerm i j 1 = j := by
  simp [pairPerm, Equiv.trans_apply]

/-- Saturation propagates from the matrix bound to either two-row factor.
The nonzero-row assumption is needed for the cancellation. -/
theorem critical_first_pair_saturated (A : Mat) (hn : NonzeroRows A)
    (he : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A) :
    overlap (A 0) (A 1) = 4*collision (A 0) (A 1) := by
  let F : Row → Row → ℝ := fun a b => symEnergy a b + (1/2 : ℝ)*altEnergy a b
  have hb1 : F (A 0) (A 1) ≤ (3/2 : ℝ)*(rowSq (A 0)*rowSq (A 1)) := by
    have h := pair_bound (A 0) (A 1) (1/2)
    norm_num [sharpConstant] at h
    exact h
  have hb2 : F (A 2) (A 3) ≤ (3/2 : ℝ)*(rowSq (A 2)*rowSq (A 3)) := by
    have h := pair_bound (A 2) (A 3) (1/2)
    norm_num [sharpConstant] at h
    exact h
  have hf1 : 0 ≤ F (A 0) (A 1) :=
    add_nonneg (symEnergy_nonneg _ _) (mul_nonneg (by norm_num) (altEnergy_nonneg _ _))
  have hp2 : 0 < (3/2 : ℝ)*(rowSq (A 2)*rowSq (A 3)) :=
    mul_pos (by norm_num) (mul_pos ((rowSq_pos_iff _).mpr (hn 2))
      ((rowSq_pos_iff _).mpr (hn 3)))
  have hw := weighted_laplace_bound A (1/2) (by norm_num)
  rw [he] at hw
  have hid : ((3/2 : ℝ)*rowProduct A)^2 =
      ((3/2 : ℝ)*(rowSq (A 0)*rowSq (A 1))) *
      ((3/2 : ℝ)*(rowSq (A 2)*rowSq (A 3))) := by
    rw [mul_pow, rowProduct_sq]; ring
  rw [hid] at hw
  have hs : ((3/2 : ℝ)*(rowSq (A 0)*rowSq (A 1))) *
      ((3/2 : ℝ)*(rowSq (A 2)*rowSq (A 3))) ≤
      F (A 0) (A 1) * ((3/2 : ℝ)*(rowSq (A 2)*rowSq (A 3))) :=
    hw.trans (mul_le_mul_of_nonneg_left hb2 hf1)
  have heF := le_antisymm hb1 (le_of_mul_le_mul_right hs hp2)
  dsimp [F] at heF
  rw [symEnergy_identity, altEnergy_identity] at heF
  linarith

/-- Critical equality forces all six actual row-product constraints. -/
theorem critical_equality_constant_products (A : Mat) (hn : NonzeroRows A)
    (he : ‖A.permanent‖ + (1/2 : ℝ)*‖A.det‖ = (3/2 : ℝ)*rowProduct A) :
    ConstantRowProducts A := by
  intro i j hij
  let σ := pairPerm i j
  let B : Mat := A.submatrix σ id
  have hBn : NonzeroRows B := fun r => hn (σ r)
  have hBe : ‖B.permanent‖ + (1/2 : ℝ)*‖B.det‖ = (3/2 : ℝ)*rowProduct B := by
    simpa only [B, Matrix.permanent_permute_cols, det_norm_permute,
      rowProduct_permute] using he
  have h := (collision_eq_iff_products_constant (B 0) (B 1)).mp
    (critical_first_pair_saturated B hBn hBe)
  simpa only [B, σ, Matrix.submatrix_apply, id_eq, pairPerm_zero i j hij,
    pairPerm_one] using h

#print axioms critical_equality_constant_products
end
end FourRowTradeoff
