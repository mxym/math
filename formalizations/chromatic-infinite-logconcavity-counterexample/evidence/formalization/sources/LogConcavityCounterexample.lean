import ChromaticPolynomial

namespace ChromaticC17
open SimpleGraph Polynomial

/-- Absolute coefficients in ascending degree; polynomial coefficients supply the zero tail. -/
def absCoefficients (P : ℤ[X]) (k : ℕ) : ℤ := |P.coeff k|

/-- Endpoint-retaining log-concavity operator with the left boundary a(-1) = 0. -/
def logConcavityOp (a : ℕ → ℤ) (k : ℕ) : ℤ :=
  a k ^ 2 - (if k = 0 then 0 else a (k - 1)) * a (k + 1)

noncomputable def logConcavityIterate (a : ℕ → ℤ) : ℕ → (ℕ → ℤ)
  | 0 => a
  | r + 1 => logConcavityOp (logConcavityIterate a r)

def InfinitelyLogConcave (a : ℕ → ℤ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ k : ℕ, 0 ≤ logConcavityIterate a r k

theorem logConcavityOp_zero_tail (a : ℕ → ℤ) (N : ℕ)
    (h : ∀ k, N < k → a k = 0) : ∀ k, N < k → logConcavityOp a k = 0 := by
  intro k hk
  simp [logConcavityOp, h k hk, h (k + 1) (by omega)]

theorem logConcavityIterate_zero_tail (a : ℕ → ℤ) (N : ℕ)
    (h : ∀ k, N < k → a k = 0) (r : ℕ) :
    ∀ k, N < k → logConcavityIterate a r k = 0 := by
  induction r with
  | zero => exact h
  | succ r ih => exact logConcavityOp_zero_tail _ N ih

theorem cyclePolynomial_coeff (k : ℕ) :
    cyclePolynomial.coeff k = (-1 : ℤ) ^ (17 - k) * (Nat.choose 17 k : ℤ) -
      (if k = 1 then 1 else 0) + (if k = 0 then 1 else 0) := by
  have he : (X - 1 : ℤ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [cyclePolynomial, he]
  simp only [coeff_sub, coeff_X_add_C_pow, coeff_add, coeff_X, coeff_C]
  split_ifs <;> omega

theorem cyclePolynomial_zero_tail (k : ℕ) (hk : 17 < k) : cyclePolynomial.coeff k = 0 := by
  rw [cyclePolynomial_coeff, Nat.choose_eq_zero_of_lt hk]
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [h0, h1]

/-- All iterates retain the same finite right endpoint, as in the finite-sequence convention. -/
theorem cyclePolynomial_iterate_zero_tail (r k : ℕ) (hk : 17 < k) :
    logConcavityIterate (absCoefficients cyclePolynomial) r k = 0 := by
  apply logConcavityIterate_zero_tail _ 17 _ r k hk
  intro j hj
  simp [absCoefficients, cyclePolynomial_zero_tail j hj]

theorem absCoefficients_zero : absCoefficients cyclePolynomial 0 = 0 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]
theorem absCoefficients_one : absCoefficients cyclePolynomial 1 = 16 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]
theorem absCoefficients_two : absCoefficients cyclePolynomial 2 = 136 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]
theorem absCoefficients_three : absCoefficients cyclePolynomial 3 = 680 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]
theorem absCoefficients_four : absCoefficients cyclePolynomial 4 = 2380 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]
theorem absCoefficients_five : absCoefficients cyclePolynomial 5 = 6188 := by
  norm_num [absCoefficients, cyclePolynomial_coeff, Nat.choose]

/-- Exact third-iterate certificate derived from the actual polynomial's absolute coefficients. -/
theorem third_iterate_value :
    logConcavityIterate (absCoefficients cyclePolynomial) 3 2 = -28272276537344 := by
  norm_num [logConcavityIterate, logConcavityOp, absCoefficients_zero,
    absCoefficients_one, absCoefficients_two, absCoefficients_three,
    absCoefficients_four, absCoefficients_five]

theorem cyclePolynomial_not_infinitelyLogConcave :
    ¬ InfinitelyLogConcave (absCoefficients cyclePolynomial) := by
  intro h
  have hn := h 3 (by omega) 2
  rw [third_iterate_value] at hn
  norm_num at hn

theorem every_C17_chromatic_polynomial_fails (P : ℤ[X]) (hP : IsChromaticPolynomial C17 P) :
    ¬ InfinitelyLogConcave (absCoefficients P) := by
  rw [hP.unique cyclePolynomial_isChromatic]
  exact cyclePolynomial_not_infinitelyLogConcave

/-- The conjecture on all finite simple graphs and all polynomials satisfying the color-count law. -/
def ChromaticInfiniteLogConcavityConjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (P : ℤ[X]),
    IsChromaticPolynomial G P → InfinitelyLogConcave (absCoefficients P)

theorem cycle_connected : C17.Connected := cycleGraph_connected

/-- Complete counterexample: an actual connected cycle, its coloring-count polynomial, and a negative iterate. -/
theorem explicit_counterexample :
    C17.Connected ∧ IsChromaticPolynomial C17 cyclePolynomial ∧
    logConcavityIterate (absCoefficients cyclePolynomial) 3 2 < 0 := by
  refine ⟨cycle_connected, cyclePolynomial_isChromatic, ?_⟩
  rw [third_iterate_value]
  norm_num

theorem chromatic_infinite_logconcavity_conjecture_false :
    ¬ ChromaticInfiniteLogConcavityConjecture := by
  intro h
  exact cyclePolynomial_not_infinitelyLogConcave (h 17 C17 cyclePolynomial cyclePolynomial_isChromatic)

end ChromaticC17
