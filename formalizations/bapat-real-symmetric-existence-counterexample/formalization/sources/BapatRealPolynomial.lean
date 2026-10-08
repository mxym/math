import BapatFiniteRankEndpoint

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def qPolynomial (A : Matrix (Fin n) (Fin n) R) : Polynomial R :=
  ∑ σ : Equiv.Perm (Fin n),
    Polynomial.C (permutationWeight A σ) * Polynomial.X ^ originalInversions σ

theorem qPolynomial_eval (A : Matrix (Fin n) (Fin n) R) (q : R) :
    (qPolynomial A).eval q = BapatRankTwo.qPermanent A q := by
  classical
  simp only [qPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, BapatRankTwo.qPermanent]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ hσ
  exact mul_comm _ _

theorem qPolynomial_derivative_one (A : Matrix (Fin n) (Fin n) R) :
    (qPolynomial A).derivative.eval 1 = weightedInversionSum A := by
  classical
  simp only [qPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, weightedInversionSum]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ hσ
  exact mul_comm _ _

/-- Equation (4) for the actual real q-permanent polynomial, arbitrary finite rank. -/
theorem real_endpoint_fischer {C : Type*} [Fintype C] [LinearOrder C]
    (v : Fin n → C → ℝ) :
    2 * (qPolynomial (gram v)).derivative.eval 1 =
      (n.choose 2 : ℝ) * fischerNormSq (formsProduct v) -
        ∑ c ∈ originalPairs (ι := C), fischerNormSq (wedgePolynomial v c.1 c.2) := by
  rw [qPolynomial_derivative_one]
  simpa only [Fintype.card_fin, fischerNormSq] using finiteRank_fischer_inversion_identity v

/-- Exact homogeneity used when clearing rational matrix denominators. -/
theorem qPolynomial_scale (A : Matrix (Fin n) (Fin n) R) (d : R) :
    qPolynomial (fun i j => d * A i j) = Polynomial.C (d ^ n) * qPolynomial A := by
  classical
  simp only [qPolynomial, permutationWeight, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

theorem qPermanent_scale (A : Matrix (Fin n) (Fin n) R) (d q : R) :
    BapatRankTwo.qPermanent (fun i j => d * A i j) q =
      d ^ n * BapatRankTwo.qPermanent A q := by
  have h := congrArg (fun P : Polynomial R => P.eval q) (qPolynomial_scale A d)
  apply (qPolynomial_eval (fun i j : Fin n => d * A i j) q).symm.trans
  apply h.trans
  rw [Polynomial.eval_mul, Polynomial.eval_C, qPolynomial_eval]

theorem qPolynomial_derivative_scale (A : Matrix (Fin n) (Fin n) R) (d q : R) :
    (qPolynomial (fun i j => d * A i j)).derivative.eval q =
      d ^ n * (qPolynomial A).derivative.eval q := by
  rw [qPolynomial_scale, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]

end BapatFiniteRank
