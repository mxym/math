import MatrixPerturbation
import PolynomialBounds
import InversionBounds

open scoped BigOperators
open Set

namespace BapatBounds

theorem realPolynomial_qPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    realPolynomial Bapat.inversionCount (fun σ => (Bapat.permutationWeight A σ).re) q =
      (Bapat.qPermanent A (q : ℂ)).re := by
  simp [realPolynomial, Bapat.qPermanent, Complex.mul_re, ← Complex.ofReal_pow]

theorem realDerivative_endpoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    realDerivative Bapat.inversionCount (fun σ => (Bapat.permutationWeight A σ).re) 1 =
      (Bapat.endpointDerivative A).re := by
  simp [realDerivative, Bapat.endpointDerivative, Complex.mul_re]

theorem real_permutation_coefficient_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (σ : Equiv.Perm (Fin n)) :
    |(Bapat.permutationWeight A σ).re| ≤ R ^ n := by
  apply (Complex.abs_re_le_norm _).trans
  simpa [Bapat.permutationWeight] using
    product_norm_bound Finset.univ (fun i => A i (σ i)) R hR (fun i _ => hA i (σ i))

/-- The actual inversion-weighted endpoint derivative obeys the exact bound
used to make the rank-two complex witness positive definite. -/
theorem endpointDerivative_perturbation_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R t : ℝ)
    (hR : 0 ≤ R) (hA : ∀ i j, ‖A i j‖ ≤ R) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖Bapat.endpointDerivative (diagonalPerturbation A t) - Bapat.endpointDerivative A‖ ≤
      (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * t * (R + 1) ^ (n - 1) := by
  exact weightedEndpoint_perturbation_bound Bapat.inversionCount (n.choose 2)
    inversionCount_le_choose A R t hR hA ht ht1

/-- The original qPermanent itself, with the stated explicit interval. -/
theorem qPermanent_explicit_reverse_interval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative A).re ≤ -(1 / 4 : ℝ))
    (hK : 1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * R ^ n) :
    let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * R ^ n
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    0 < q₀ ∧ q₀ < 1 ∧ h / 8 ≤
      (Bapat.qPermanent A (q₀ : ℂ)).re - (Bapat.qPermanent A 1).re ∧
      (Bapat.qPermanent A 1).re < (Bapat.qPermanent A (q₀ : ℂ)).re := by
  classical
  let e := Bapat.inversionCount (n := n)
  let c := fun σ : Equiv.Perm (Fin n) => (Bapat.permutationWeight A σ).re
  let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) * (n.factorial : ℝ) * R ^ n
  have hv : ∀ q ∈ Icc (0 : ℝ) 1,
      |realDerivative e c q - realDerivative e c 1| ≤ K * (1 - q) := by
    intro q hq
    have hh := realDerivative_difference_bound e c (n.choose 2) (R ^ n) q
      (pow_nonneg hR _) inversionCount_le_choose
      (real_permutation_coefficient_bound A R hR hA) hq.1 hq.2
    simpa [K, Fintype.card_perm, mul_assoc, mul_left_comm, mul_comm] using hh
  have hd : ∀ q, HasDerivAt (realPolynomial e c) (realDerivative e c q) q :=
    realPolynomial_hasDerivAt e c
  have he1 : realDerivative e c 1 ≤ -(1 / 4 : ℝ) := by
    simpa [e, c, realDerivative_endpoint] using h1
  have hh := explicit_reverse_interval (realPolynomial e c) (realDerivative e c) K hK hd he1 hv
  simpa [e, c, K, realPolynomial_qPermanent] using hh

end BapatBounds
