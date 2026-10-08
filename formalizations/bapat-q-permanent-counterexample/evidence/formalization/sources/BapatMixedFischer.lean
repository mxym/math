import BapatPermanentFischer

namespace BapatFischer

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators Nat

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommSemiring R]

/-- A permanent whose row and column labels may be different finite types.
This is the natural object left after deleting two rows and two columns. -/
def mixedPermanent (M : ι → κ → R) : R :=
  ∑ e : ι ≃ κ, ∏ i, M i (e i)

/-- Any choice of row/column relabeling identifies the mixed permanent with
the genuine mathlib permanent. -/
theorem mixedPermanent_eq_permanent (e₀ : ι ≃ κ) (M : ι → κ → R) :
    mixedPermanent M = Matrix.permanent (fun i j => M i (e₀ j)) := by
  classical
  unfold mixedPermanent
  calc
    (∑ e : ι ≃ κ, ∏ i, M i (e i)) =
        ∑ σ : Equiv.Perm ι, ∏ i, M i (e₀ (σ i)) := by
      symm
      apply Fintype.sum_equiv (Equiv.equivCongr (Equiv.refl ι) e₀)
      intro σ
      simp
    _ = Matrix.permanent (fun i j => M i (e₀ j)) := by
      change Matrix.permanent (Matrix.transpose (fun i j => M i (e₀ j))) = _
      exact Matrix.permanent_transpose (fun i j => M i (e₀ j))

theorem twoColorProduct_comp (e₀ : ι ≃ κ) (a b : κ → R) :
    twoColorProduct (a ∘ e₀) (b ∘ e₀) = twoColorProduct a b := by
  unfold twoColorProduct
  exact e₀.prod_comp (fun i => C (a i) + C (b i) * X)

/-- Mixed Gram/Fischer identity with arbitrary, equally sized row and column
index types. The final coefficient expression is independent of the supplied
equivalence, as required for complementary row/column minors. -/
theorem mixedPermanent_twoColor (e₀ : ι ≃ κ) (a b : ι → R) (c d : κ → R) :
    mixedPermanent (fun i j => a i * c j + b i * d j) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((Nat.factorial k) * (Nat.factorial (Fintype.card ι - k)) : ℕ) *
          (twoColorProduct a b).coeff k * (twoColorProduct c d).coeff k := by
  rw [mixedPermanent_eq_permanent e₀]
  change Matrix.permanent (fun i j => a i * (c ∘ e₀) j + b i * (d ∘ e₀) j) = _
  rw [permanent_twoColor, twoColorProduct_comp]

/-- The complex Fischer pairing, linear in its first argument. -/
noncomputable def fischerPair (n : ℕ) (p q : ℂ[X]) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.factorial (n - k)) * (Nat.factorial k) : ℕ) * p.coeff k * star (q.coeff k)

theorem mixedPermanent_gram (e₀ : ι ≃ κ) (a b : ι → ℂ) (c d : κ → ℂ) :
    mixedPermanent (fun i j => a i * star (c j) + b i * star (d j)) =
      fischerPair (Fintype.card ι) (twoColorProduct a b) (twoColorProduct c d) := by
  rw [mixedPermanent_twoColor e₀]
  simp only [fischerPair, coeff_twoColorProduct_star]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.mul_comm (Nat.factorial k) (Nat.factorial (Fintype.card ι - k))]

theorem fischerPair_self (n : ℕ) (p : ℂ[X]) :
    fischerPair n p p = (fischerNormSq n p : ℂ) := by
  simp only [fischerPair, fischerNormSq, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  push_cast
  ring

theorem fischerPair_sum_left {τ : Type*} (s : Finset τ) (n : ℕ)
    (p : τ → ℂ[X]) (q : ℂ[X]) :
    fischerPair n (∑ i ∈ s, p i) q = ∑ i ∈ s, fischerPair n (p i) q := by
  simp only [fischerPair, Polynomial.finsetSum_coeff, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem fischerPair_sum_right {τ : Type*} (s : Finset τ) (n : ℕ)
    (p : ℂ[X]) (q : τ → ℂ[X]) :
    fischerPair n p (∑ i ∈ s, q i) = ∑ i ∈ s, fischerPair n p (q i) := by
  simp only [fischerPair, Polynomial.finsetSum_coeff, star_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem fischerPair_C_mul_left (n : ℕ) (z : ℂ) (p q : ℂ[X]) :
    fischerPair n (C z * p) q = z * fischerPair n p q := by
  simp only [fischerPair, Polynomial.coeff_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem fischerPair_C_mul_right (n : ℕ) (z : ℂ) (p q : ℂ[X]) :
    fischerPair n p (C z * q) = star z * fischerPair n p q := by
  simp only [fischerPair, Polynomial.coeff_C_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem fischerNormSq_nonneg (n : ℕ) (p : ℂ[X]) : 0 ≤ fischerNormSq n p := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

end BapatFischer
