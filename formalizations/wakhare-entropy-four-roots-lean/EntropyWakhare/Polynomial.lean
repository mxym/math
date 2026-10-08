import EntropyWakhare.FourRoots
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace EntropyRoot

open Polynomial

/-- The actual polynomial form of Wakhare's h_{11,s}. -/
noncomputable def hPolynomial (s : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range 11, C (innerCoeff s j : ℝ) * X^(s*j)

theorem eval_hPolynomial (s : ℕ) (x : ℝ) :
    (hPolynomial s).eval x = hReal s x := by
  classical
  simp only [hPolynomial, hReal, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Original entropy polynomial p_{11,10}, not an interpolating surrogate. -/
noncomputable def witnessPolynomial : ℝ[X] :=
  C alpha * (C 11 * (1-X^10)^11 * hPolynomial 11) -
    C 10 * (1-X^11)^11 * hPolynomial 10

theorem eval_witnessPolynomial (x : ℝ) :
    witnessPolynomial.eval x = entropyPolynomial x := by
  simp [witnessPolynomial, entropyPolynomial, AReal, BReal, eval_hPolynomial]

/-- Exact refutation: at least four strictly ordered roots of the polynomial. -/
theorem actual_polynomial_has_four_distinct_roots :
    ∃ z₁ z₂ z₃ z₄ : ℝ,
      0 < z₁ ∧ z₁ < z₂ ∧ z₂ < z₃ ∧ z₃ < z₄ ∧ z₄ < 1 ∧
      witnessPolynomial.eval z₁ = 0 ∧ witnessPolynomial.eval z₂ = 0 ∧
      witnessPolynomial.eval z₃ = 0 ∧ witnessPolynomial.eval z₄ = 0 := by
  simpa only [eval_witnessPolynomial] using four_distinct_interior_roots

end EntropyRoot
