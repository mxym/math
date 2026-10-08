import QPermanent
import EndpointIdentity
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators
open Finset
namespace Bapat

/-- The actual determinant of the indicated ordered two-by-two minor. -/
def pairDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n) : ℂ :=
  Matrix.det (fun r c : Fin 2 => A (if r = 0 then i else j) (if c = 0 then k else l))

 theorem pairDeterminant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n) :
    pairDeterminant A i j k l = A i k * A j l - A i l * A j k := by
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    fun r c => A (if r = 0 then i else j) (if c = 0 then k else l)
  simpa [pairDeterminant, M] using Matrix.det_fin_two M

/-- The paper's signed deleted-minor sum, with actual determinants and actual permanents. -/
def endpointDefect {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ∑ k : Fin n, ∑ l : Fin n,
    if k < l then pairDeterminant A i j k l * minorPermanent A i j k l else 0 else 0

 theorem sum_row_pairs_const {n : ℕ} (c : ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then c else 0) =
      ((n * (n - 1) / 2 : ℕ) : ℂ) * c := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => if p.1 < p.2 then c else 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]

 theorem endpointDerivative_defect_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    2 * endpointDerivative A = ((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent -
      endpointDefect A := by
  have hexp :
      (∑ i : Fin n, ∑ j : Fin n, if i < j then ∑ k : Fin n, ∑ l : Fin n,
        if k < l then (A i k * A j l + A i l * A j k) *
          minorPermanent A i j k l else 0 else 0) =
      ((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent := by
    rw [← sum_row_pairs_const]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, ite_true]
      exact (permanent_two_rows A (ne_of_lt hij)).symm
    · simp [hij]
  rw [endpointDerivative_minor_formula, ← hexp]
  unfold endpointDefect
  simp_rw [pairDeterminant_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ite_true]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hkl : k < l <;> simp [hkl] <;> ring
  · simp [hij]

/-- The direct analytic version of the endpoint identity. -/
 theorem hasDerivAt_qPermanent_defect {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (qPermanent A)
      ((((n * (n - 1) / 2 : ℕ) : ℂ) * A.permanent - endpointDefect A) / 2) 1 := by
  convert hasDerivAt_qPermanent_one A using 1
  have h := endpointDerivative_defect_identity A
  apply (div_eq_iff (two_ne_zero : (2 : ℂ) ≠ 0)).2
  simpa [mul_comm] using h.symm

end Bapat
