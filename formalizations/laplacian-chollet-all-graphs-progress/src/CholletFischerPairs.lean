import CholletFischer

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial BapatFiniteRank

namespace Chollet

variable {C : Type*} [Fintype C] [DecidableEq C]
noncomputable section

def directional (u : C → ℝ) (p : MvPolynomial C ℝ) : MvPolynomial C ℝ :=
  ∑ i, MvPolynomial.C (u i) * pderiv i p

def scalarProduct (u v : C → ℝ) : ℝ := ∑ i, u i * v i

theorem linearForm_eq (u : C → ℝ) :
    linearForm u = ∑ i, MvPolynomial.C (u i) * X i := by
  simp [linearForm, X, C_mul_monomial]

theorem pderiv_linearForm (i : C) (u : C → ℝ) :
    pderiv i (linearForm u) = MvPolynomial.C (u i) := by
  rw [linearForm_eq, map_sum]
  simp [pderiv_C_mul, pderiv_X, Pi.single_apply, eq_comm]

theorem directional_mul (u : C → ℝ) (p q : MvPolynomial C ℝ) :
    directional u (p * q) = directional u p * q + p * directional u q := by
  simp only [directional, pderiv_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem directional_linearForm (u v : C → ℝ) :
    directional u (linearForm v) = MvPolynomial.C (scalarProduct u v) := by
  simp only [directional, pderiv_linearForm, ← map_mul, ← map_sum, scalarProduct]

theorem scalarProduct_comm (u v : C → ℝ) : scalarProduct u v = scalarProduct v u := by
  simp [scalarProduct, mul_comm]

theorem scalarProduct_self_nonneg (u : C → ℝ) : 0 ≤ scalarProduct u u := by
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

theorem pair_linearForm_mul (u : C → ℝ) (p q : MvPolynomial C ℝ) :
    fischerPair (linearForm u * p) q = fischerPair p (directional u q) := by
  rw [linearForm_eq]
  simp only [Finset.sum_mul, fischerPair_sum_left, directional, fischerPair_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, fischerPair_C_mul_left, pair_X_mul, fischerPair_C_mul_right]

theorem pair_directional (u : C → ℝ) (p q : MvPolynomial C ℝ) :
    fischerPair (directional u p) q = fischerPair p (linearForm u * q) := by
  rw [pair_comm, ← pair_linearForm_mul, pair_comm]

theorem pair_linearForm_mul_linearForm_mul (u v : C → ℝ)
    (p q : MvPolynomial C ℝ) :
    fischerPair (linearForm u * p) (linearForm v * q) =
      scalarProduct u v * fischerPair p q +
        fischerPair (directional v p) (directional u q) := by
  rw [pair_linearForm_mul, directional_mul, directional_linearForm,
    fischerPair_add_right, fischerPair_C_mul_right, ← pair_directional]

theorem linear_factor_norm_identity (u : C → ℝ) (q : MvPolynomial C ℝ) :
    fischerPair (linearForm u * q) (linearForm u * q) =
      scalarProduct u u * fischerPair q q +
        fischerPair (directional u q) (directional u q) :=
  pair_linearForm_mul_linearForm_mul u u q q

theorem linear_factor_norm_bound (u : C → ℝ) (q : MvPolynomial C ℝ) :
    scalarProduct u u * fischerPair q q ≤
      fischerPair (linearForm u * q) (linearForm u * q) := by
  rw [linear_factor_norm_identity]
  exact le_add_of_nonneg_right (pair_self_nonneg _)

theorem pair_sum_self (a b : MvPolynomial C ℝ) :
    fischerPair (a + b) (a + b) =
      fischerPair a a + 2 * fischerPair a b + fischerPair b b := by
  rw [fischerPair_add_left, fischerPair_add_right, fischerPair_add_right,
    pair_comm b a]
  ring

theorem pair_scaled_sum_self (a b : MvPolynomial C ℝ) (s t : ℝ) :
    fischerPair (MvPolynomial.C s * a + MvPolynomial.C t * b)
      (MvPolynomial.C s * a + MvPolynomial.C t * b) =
    s ^ 2 * fischerPair a a + 2 * s * t * fischerPair a b +
      t ^ 2 * fischerPair b b := by
  rw [pair_sum_self]
  simp only [fischerPair_C_mul_left, fischerPair_C_mul_right]
  ring

theorem sum_pair_scaled_self (u v : C → ℝ) (a b : MvPolynomial C ℝ) :
    (∑ i, fischerPair (MvPolynomial.C (u i) * a + MvPolynomial.C (v i) * b)
      (MvPolynomial.C (u i) * a + MvPolynomial.C (v i) * b)) =
    scalarProduct u u * fischerPair a a +
      2 * scalarProduct u v * fischerPair a b +
      scalarProduct v v * fischerPair b b := by
  simp only [pair_scaled_sum_self, Finset.sum_add_distrib, scalarProduct,
    Finset.sum_mul, Finset.mul_sum, pow_two]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

/-- The exact degree-two normal-order identity. Its remainder is an explicit
sum of Fischer squared norms, valid for an arbitrary real polynomial q. -/
theorem quadratic_factor_norm_identity (u v : C → ℝ) (q : MvPolynomial C ℝ) :
    fischerPair (linearForm u * (linearForm v * q))
      (linearForm u * (linearForm v * q)) =
    (scalarProduct u u * scalarProduct v v + (scalarProduct u v)^2) *
      fischerPair q q +
    (∑ i, fischerPair
      (MvPolynomial.C (u i) * directional v q + MvPolynomial.C (v i) * directional u q)
      (MvPolynomial.C (u i) * directional v q + MvPolynomial.C (v i) * directional u q)) +
    fischerPair (directional v (directional u q)) (directional v (directional u q)) := by
  rw [linear_factor_norm_identity, linear_factor_norm_identity, directional_mul,
    directional_linearForm, pair_sum_self]
  simp only [fischerPair_C_mul_left, fischerPair_C_mul_right]
  rw [linear_factor_norm_identity, ← pair_directional, sum_pair_scaled_self]
  ring

theorem quadratic_factor_norm_bound (u v : C → ℝ) (q : MvPolynomial C ℝ) :
    (scalarProduct u u * scalarProduct v v + (scalarProduct u v)^2) *
      fischerPair q q ≤
    fischerPair (linearForm u * (linearForm v * q))
      (linearForm u * (linearForm v * q)) := by
  rw [quadratic_factor_norm_identity]
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => pair_self_nonneg
      (MvPolynomial.C (u i) * directional v q + MvPolynomial.C (v i) * directional u q))
  linarith [pair_self_nonneg (directional v (directional u q))]

end
end Chollet
