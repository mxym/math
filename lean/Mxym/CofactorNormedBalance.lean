import Mxym.Determinant
import Mxym.NormedBalance

/-! The existing determinant cofactor relation is pushed through an explicit
real linear equivalence into a normed space. Normalization supplies balance;
none of these new corollaries assumes the balance inequality itself. -/
namespace Mxym.Determinant
open scoped BigOperators Classical
open Mxym.Rademacher
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def column {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ) (j : Fin (d + 1)) :
    Fin d → ℝ := fun i => x i j

theorem cofactor_vector_relation {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ) :
    ∑ j, cofactor x j • column x j = 0 := by
  funext i
  simpa [column, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    horizontal_cofactor_relation x i

theorem mapped_cofactor_relation {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (φ : (Fin d → ℝ) ≃ₗ[ℝ] E) :
    ∑ j, cofactor x j • φ (column x j) = 0 := by
  have h := congrArg φ (cofactor_vector_relation x)
  simpa only [map_sum, map_smul, map_zero] using h

theorem cofactor_balance_of_normalized_columns {d : ℕ}
    (x : Matrix (Fin d) (Fin (d + 1)) ℝ) (φ : (Fin d → ℝ) ≃ₗ[ℝ] E)
    (hunit : ∀ j, cofactor x j ≠ 0 → ‖φ (column x j)‖ = 1) :
    ∀ i, |cofactor x i| ≤ (∑ j, |cofactor x j|) / 2 := by
  exact Mxym.NormedBalance.coefficient_balance (cofactor x)
    (fun j => φ (column x j)) (mapped_cofactor_relation x φ) hunit

theorem normalized_sign_average_bound {d : ℕ}
    (x : Matrix (Fin d) (Fin (d + 1)) ℝ) (φ : (Fin d → ℝ) ≃ₗ[ℝ] E)
    (hunit : ∀ j, cofactor x j ≠ 0 → ‖φ (column x j)‖ = 1) :
    (∑ ε : Fin (d + 1) → Bool,
      |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det|) /
      Fintype.card (Fin (d + 1) → Bool) ≤ (∑ j, |cofactor x j|) / 2 := by
  exact balanced_sign_average_bound x (cofactor_balance_of_normalized_columns x φ hunit)

theorem normalized_sign_average_equality_iff {d : ℕ}
    (x : Matrix (Fin d) (Fin (d + 1)) ℝ) (φ : (Fin d → ℝ) ≃ₗ[ℝ] E)
    (hunit : ∀ j, cofactor x j ≠ 0 → ‖φ (column x j)‖ = 1) :
    ((∑ ε : Fin (d + 1) → Bool,
      |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det|) /
      Fintype.card (Fin (d + 1) → Bool) = (∑ j, |cofactor x j|) / 2) ↔
      Fintype.card {j // cofactor x j ≠ 0} ≤ 3 ∨
        ∃ j, |cofactor x j| = (∑ k, |cofactor x k|) / 2 := by
  exact balanced_sign_average_equality_iff x
    (cofactor_balance_of_normalized_columns x φ hunit)

end Mxym.Determinant
