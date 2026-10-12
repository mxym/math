import Entry002.ArithmeticSplittingCount
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! Actual prime-ideal counting and logarithmic prime-power coefficients.

The natural prime-ideal PNT below is an open proposition, not a theorem.
The coefficients sum over genuine nonzero prime ideals of the ring of integers;
positive powers are detected explicitly, with no analytic conclusion in their
definition.  Since a nonzero prime ideal has norm at least two, the positive
exponent is unique. -/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The exact remaining natural prime-ideal counting asymptotic for `K`. -/
def PrimeIdealNaturalPNT : Prop :=
  Tendsto (fun x : ℝ =>
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
    atTop (nhds 1)

/-- The universal premise of the third-round conditional main theorem.
This proposition is defined and is not asserted to hold. -/
def NumberFieldPrimeIdealPNTTarget : Prop :=
  ∀ (N : Type) [Field N] [NumberField N], PrimeIdealNaturalPNT N

/-- Genuine nonzero prime ideals whose norm has a positive power equal to `n`. -/
def primeIdealPowerSupport (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (nonzeroPrimeIdealsUpTo K n).filter
    (fun P => ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n)

@[simp] theorem mem_primeIdealPowerSupport (n : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ primeIdealPowerSupport K n ↔
      Ideal.absNorm P ≤ n ∧ P.IsPrime ∧ P ≠ ⊥ ∧
        ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n := by
  simp [primeIdealPowerSupport, and_assoc]

/-- The true number-field von Mangoldt coefficient:
`∑_{N(P)^k=n, k>0} log N(P)`, with each prime ideal occurring once. -/
def primeIdealVonMangoldt (n : ℕ) : ℝ :=
  ∑ P ∈ primeIdealPowerSupport K n, Real.log (Ideal.absNorm P : ℝ)

/-- The true weighted prime-ideal-power count at a real endpoint. -/
def primeIdealPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, primeIdealVonMangoldt K n

/-- The logarithmically weighted count of actual nonzero prime ideals. -/
def primeIdealTheta (x : ℝ) : ℝ :=
  ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, Real.log (Ideal.absNorm P : ℝ)

theorem primeIdeal_absNorm_two_le (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  let : P.IsMaximal := hprime.isMaximal hne
  obtain ⟨p, k, hk, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [hnorm]
  exact hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.pos hk)

theorem primeIdealVonMangoldt_nonneg (n : ℕ) :
    0 ≤ primeIdealVonMangoldt K n := by
  apply Finset.sum_nonneg
  intro P hP
  obtain ⟨_, hprime, hne, _⟩ := (mem_primeIdealPowerSupport K n P).mp hP
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ Ideal.absNorm P from
    (by omega : 1 ≤ 2).trans (primeIdeal_absNorm_two_le K P hprime hne))

theorem primeIdealPowerSupport_eq_empty_of_lt_two (n : ℕ) (hn : n < 2) :
    primeIdealPowerSupport K n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨hle, hprime, hne, _⟩ := (mem_primeIdealPowerSupport K n P).mp hP
  have := primeIdeal_absNorm_two_le K P hprime hne
  omega

theorem primeIdealVonMangoldt_eq_zero_of_lt_two (n : ℕ) (hn : n < 2) :
    primeIdealVonMangoldt K n = 0 := by
  simp [primeIdealVonMangoldt, primeIdealPowerSupport_eq_empty_of_lt_two K n hn]

/-- The logarithmic coefficient counts each prime ideal once because its
positive norm-power exponent, if it exists, is unique. -/
theorem primeIdeal_norm_power_exponent_unique (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (a b : ℕ)
    (hpow : Ideal.absNorm P ^ a = Ideal.absNorm P ^ b) : a = b :=
  Nat.pow_right_injective (primeIdeal_absNorm_two_le K P hprime hne) hpow

theorem primeIdeal_norm_power_exponent_le (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (k n : ℕ)
    (hpow : Ideal.absNorm P ^ k = n) : k ≤ n := by
  have htwo := primeIdeal_absNorm_two_le K P hprime hne
  have hpowle : 2 ^ k ≤ Ideal.absNorm P ^ k := Nat.pow_le_pow_left htwo k
  exact (Nat.lt_two_pow_self (n := k)).le.trans (hpow ▸ hpowle)

end

end Entry002
