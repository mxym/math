import Entry002.ArithmeticPrimeIdealRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Exact decomposition of actual prime-ideal counts. The finite error
bound reduces complete-splitting asymptotics to the number-field prime-ideal
theorem, which is not proved or postulated in this file. -/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- All actual nonzero prime ideals with absolute norm at most `n`. -/
def nonzeroPrimeIdealsUpTo (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter (fun P => P.IsPrime ∧ P ≠ ⊥)

@[simp] theorem mem_nonzeroPrimeIdealsUpTo (n : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ nonzeroPrimeIdealsUpTo K n ↔ Ideal.absNorm P ≤ n ∧ P.IsPrime ∧ P ≠ ⊥ := by
  simp [nonzeroPrimeIdealsUpTo]

/-- The actual ramified degree-one prime ideals below the endpoint. -/
def ramifiedDegreeOnePrimeIdeals (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter (fun P => P.IsPrime ∧
    (Ideal.absNorm P).Prime ∧
      ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {((Ideal.absNorm P : ℕ) : ℤ)}))

@[simp] theorem mem_ramifiedDegreeOnePrimeIdeals (n : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ ramifiedDegreeOnePrimeIdeals K n ↔ Ideal.absNorm P ≤ n ∧ P.IsPrime ∧
      (Ideal.absNorm P).Prime ∧
        ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {((Ideal.absNorm P : ℕ) : ℤ)}) := by
  simp [ramifiedDegreeOnePrimeIdeals]

/-- A fixed genuine finite discriminant-exception bound; it is independent
of the endpoint and all later choices of walks. -/
def discriminantIdealCount : ℕ :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (NumberField.discr K).natAbs).toFinset.card

theorem ramifiedDegreeOnePrimeIdeals_card_le (n : ℕ) :
    (ramifiedDegreeOnePrimeIdeals K n).card ≤ discriminantIdealCount K := by
  apply Finset.card_le_card
  intro P hP
  obtain ⟨_, hprime, hp, hram⟩ := (mem_ramifiedDegreeOnePrimeIdeals K n P).mp hP
  rw [Set.Finite.mem_toFinset]
  have hdiv : ((Ideal.absNorm P : ℕ) : ℤ) ∣ NumberField.discr K := by
    by_contra hnotdiv
    exact hram ((NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hp)).mp hnotdiv)
  have hdivNat : Ideal.absNorm P ∣ (NumberField.discr K).natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdiv
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) hdivNat

theorem nonzeroPrimeIdealsUpTo_partition (n : ℕ) :
    nonzeroPrimeIdealsUpTo K n =
      unramifiedDegreeOnePrimeIdeals K n ∪ ramifiedDegreeOnePrimeIdeals K n ∪
        higherDegreePrimeIdeals K n := by
  ext P
  simp only [Finset.mem_union, mem_nonzeroPrimeIdealsUpTo,
    mem_unramifiedDegreeOnePrimeIdeals, mem_ramifiedDegreeOnePrimeIdeals,
    mem_higherDegreePrimeIdeals]
  have hne (hp : (Ideal.absNorm P).Prime) : P ≠ ⊥ := by
    intro heq
    exact hp.ne_zero (by simp [heq])
  by_cases hp : (Ideal.absNorm P).Prime
  · by_cases hu : Algebra.IsUnramifiedIn (𝓞 K)
      (Ideal.span {((Ideal.absNorm P : ℕ) : ℤ)}) <;> simp [hp, hu, hne hp]
  · simp [hp]

/-- Exact disjoint cardinal decomposition, before any analytic limit. -/
theorem nonzeroPrimeIdealsUpTo_card [IsGalois ℚ K] (n : ℕ) :
    (nonzeroPrimeIdealsUpTo K n).card =
      Module.finrank ℚ K * ((unramifiedRationalPrimes K n).filter
        (RationalPrimeSplitsCompletely K)).card +
      (ramifiedDegreeOnePrimeIdeals K n).card + (higherDegreePrimeIdeals K n).card := by
  have hdisj₁ : Disjoint (unramifiedDegreeOnePrimeIdeals K n)
      (ramifiedDegreeOnePrimeIdeals K n) := by
    apply Finset.disjoint_left.mpr
    intro P hU hR
    exact ((mem_ramifiedDegreeOnePrimeIdeals K n P).mp hR).2.2.2
      ((mem_unramifiedDegreeOnePrimeIdeals K n P).mp hU).2.2.2
  have hdisj₂ : Disjoint
      (unramifiedDegreeOnePrimeIdeals K n ∪ ramifiedDegreeOnePrimeIdeals K n)
      (higherDegreePrimeIdeals K n) := by
    apply Finset.disjoint_left.mpr
    intro P hUR hH
    have hn := ((mem_higherDegreePrimeIdeals K n P).mp hH).2.2.2
    rcases Finset.mem_union.mp hUR with hU | hR
    · exact hn ((mem_unramifiedDegreeOnePrimeIdeals K n P).mp hU).2.2.1
    · exact hn ((mem_ramifiedDegreeOnePrimeIdeals K n P).mp hR).2.2.1
  rw [nonzeroPrimeIdealsUpTo_partition, Finset.card_union_of_disjoint hdisj₂,
    Finset.card_union_of_disjoint hdisj₁, unramifiedDegreeOnePrimeIdeals_card]

/-- The exact completely split rational-prime count differs from the
prime-ideal count, after multiplying by the degree, by a proved finite
`O(sqrt n)` error. No density assumption occurs here. -/
theorem nonzeroPrimeIdealsUpTo_splitting_error [IsGalois ℚ K] (n : ℕ) :
    0 ≤ (nonzeroPrimeIdealsUpTo K n).card -
      Module.finrank ℚ K * ((unramifiedRationalPrimes K n).filter
        (RationalPrimeSplitsCompletely K)).card ∧
    (nonzeroPrimeIdealsUpTo K n).card -
      Module.finrank ℚ K * ((unramifiedRationalPrimes K n).filter
        (RationalPrimeSplitsCompletely K)).card ≤
      discriminantIdealCount K + Module.finrank ℚ K * (Nat.sqrt n + 1) := by
  rw [nonzeroPrimeIdealsUpTo_card]
  constructor
  · exact Nat.zero_le _
  · have hram := ramifiedDegreeOnePrimeIdeals_card_le K n
    have hhigh := higherDegreePrimeIdeals_card_le K n
    omega

end

end Entry002
