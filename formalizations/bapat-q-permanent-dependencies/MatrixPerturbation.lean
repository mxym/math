import ProductBounds
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Fintype.Perm

open scoped BigOperators ComplexOrder

namespace BapatBounds

def diagonalPerturbation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  A + Matrix.diagonal (fun _ => (t : ℂ))

theorem diagonalPerturbation_difference {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (ht : 0 ≤ t) (i j : Fin n) :
    ‖diagonalPerturbation A t i j - A i j‖ ≤ t := by
  by_cases hij : i = j
  · subst j
    simp [diagonalPerturbation, Matrix.diagonal_apply, abs_of_nonneg ht]
  · simp [diagonalPerturbation, Matrix.diagonal_apply, hij, ht]

theorem diagonalPerturbation_entries {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i j, ‖diagonalPerturbation A t i j‖ ≤ R + 1 := by
  intro i j
  have hd := diagonalPerturbation_difference A t ht i j
  have heq : diagonalPerturbation A t i j =
      A i j + (diagonalPerturbation A t i j - A i j) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith [hA i j])

/-- Positive definiteness for the actual perturbed Gram matrix; no eigenvalue
or spectral gap hypothesis is supplied. -/
theorem gram_diagonalPerturbation_posDef {n r : ℕ}
    (V : Matrix (Fin n) (Fin r) ℂ) (t : ℝ) (ht : 0 < t) :
    (diagonalPerturbation (V * V.conjTranspose) t).PosDef := by
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_self_mul_conjTranspose V)
    (Matrix.PosDef.diagonal (fun _ => Complex.zero_lt_real.mpr ht))

theorem diagonalPerturbation_product_difference {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(∏ i, diagonalPerturbation A t i (σ i)) - ∏ i, A i (σ i)‖ ≤
      (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  apply permutation_product_difference _ _ σ (R + 1) t (by linarith) ht
    (diagonalPerturbation_entries A R t hA ht ht1)
    (fun i j => (hA i j).trans (by linarith))
    (diagonalPerturbation_difference A t ht)

/-- A weighted endpoint sum. Substituting inversionCount gives the actual
endpoint derivative once its combinatorial bound is proved. -/
def weightedEndpoint {n : ℕ} (e : Equiv.Perm (Fin n) → ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ, (e σ : ℂ) * ∏ i, A i (σ i)

theorem weightedEndpoint_perturbation_bound {n : ℕ}
    (e : Equiv.Perm (Fin n) → ℕ) (N : ℕ) (he : ∀ σ, e σ ≤ N)
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖weightedEndpoint e (diagonalPerturbation A t) - weightedEndpoint e A‖ ≤
      (N : ℝ) * (n.factorial : ℝ) * (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  classical
  unfold weightedEndpoint
  rw [← Finset.sum_sub_distrib]
  have hterm (σ : Equiv.Perm (Fin n)) :
      ‖(e σ : ℂ) * (∏ i, diagonalPerturbation A t i (σ i)) -
        (e σ : ℂ) * (∏ i, A i (σ i))‖ ≤
        (N : ℝ) * ((n : ℝ) * t * (R + 1) ^ (n - 1)) := by
    rw [← mul_sub, norm_mul, Complex.norm_natCast]
    exact mul_le_mul (by exact_mod_cast he σ)
      (diagonalPerturbation_product_difference A σ R t hR hA ht ht1)
      (norm_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ σ, ‖(e σ : ℂ) * (∏ i, diagonalPerturbation A t i (σ i)) -
        (e σ : ℂ) * (∏ i, A i (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (N : ℝ) * ((n : ℝ) * t * (R + 1) ^ (n - 1)) :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by simp [Fintype.card_perm, mul_assoc, mul_left_comm]

end BapatBounds
