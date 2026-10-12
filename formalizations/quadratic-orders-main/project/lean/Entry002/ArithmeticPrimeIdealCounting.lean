import Entry002.ArithmeticSupplyElementary
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual prime-ideal norm and splitting-count bridges. No prime-ideal
asymptotic or splitting-density conclusion is assumed or asserted here. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- A degree-one prime over the actual rational prime has actual norm `p`. -/
theorem arithmeticSupply_degree_one_prime_norm (p : ℕ)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hdegree : P.inertiaDeg ℤ = 1) : Ideal.absNorm P = p := by
  simpa [hdegree] using (Ideal.pow_inertiaDeg p P).symm

/-- A principal generator of that degree-one prime has genuine determinant
norm of absolute value `p`; its integrality is expressed by its type. -/
theorem arithmeticSupply_degree_one_generator_norm (p : ℕ)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hdegree : P.inertiaDeg ℤ = 1) (a : 𝓞 K)
    (hgenerator : Ideal.span ({a} : Set (𝓞 K)) = P) :
    (Algebra.norm ℤ a).natAbs = p := by
  rw [← Ideal.absNorm_span_singleton, hgenerator]
  exact arithmeticSupply_degree_one_prime_norm K p P hdegree

/-- Prime norm forces the genuine rational prime below `P` and inertia
degree one. Both conclusions use Mathlib's ideal and quotient notions. -/
theorem arithmeticSupply_prime_norm_iff_degree_one (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 K)) [P.IsPrime] :
    Ideal.absNorm P = p ↔
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ P.inertiaDeg ℤ = 1 := by
  constructor
  · intro hnorm
    have hmem : (p : 𝓞 K) ∈ P := by
      simpa only [hnorm] using P.absNorm_mem
    have hlies : P.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
        (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa using hmem)
    have := hlies
    refine ⟨hlies, Nat.pow_right_injective hp.two_le ?_⟩
    simpa only [pow_one, hnorm] using Ideal.pow_inertiaDeg p P
  · rintro ⟨hlies, hdegree⟩
    have := hlies
    exact arithmeticSupply_degree_one_prime_norm K p P hdegree

/-- Complete splitting is stated using every actual prime ideal above
the rational prime, with genuine ramification and inertia degrees. -/
def RationalPrimeSplitsCompletely (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1

/-- Over an unramified rational prime, one degree-one prime forces every
prime to have degree one in an arbitrary Galois number field. -/
theorem arithmeticSupply_degree_one_iff_splits_completely [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime)
    (hunram : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.absNorm P = p) ↔
      RationalPrimeSplitsCompletely K p := by
  constructor
  · rintro ⟨P, hprime, hnorm⟩
    have := hprime
    obtain ⟨hlies, hdegree⟩ :=
      (arithmeticSupply_prime_norm_iff_degree_one K p hp P).mp hnorm
    have := hlies
    intro Q hQ hQlies
    have := hQ
    have := hQlies
    exact ⟨hunram.ramificationIdx_eq_one hQlies,
      (Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) Q P
        (K ≃ₐ[ℚ] K)).trans hdegree⟩
  · intro hsplit
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)
    obtain ⟨P⟩ :=
      (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
    refine ⟨P.1, P.2.1, ?_⟩
    exact arithmeticSupply_degree_one_prime_norm K p P.1 (hsplit P.1 P.2.1 P.2.2).2

/-- Complete splitting gives exactly `[K:ℚ]` actual prime ideals over `p`. -/
theorem arithmeticSupply_splitting_prime_fiber_card [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime) (hsplit : RationalPrimeSplitsCompletely K p) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K := by
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 K) (K ≃ₐ[ℚ] K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P.1
    (K ≃ₐ[ℚ] K), Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P.1
    (K ≃ₐ[ℚ] K), (hsplit P.1 P.2.1 P.2.2).1, (hsplit P.1 P.2.1 P.2.2).2,
    one_mul, mul_one, IsGalois.card_aut_eq_finrank] at h
  exact h

/-- The actual prime ideals whose quotient has cardinality `p`. -/
def primeNormFiber (p : ℕ) : Set (Ideal (𝓞 K)) :=
  {P | P.IsPrime ∧ Ideal.absNorm P = p}

theorem primeNormFiber_finite (p : ℕ) : (primeNormFiber K p).Finite :=
  (Ideal.finite_setOfPred_absNorm_eq p).subset (fun _ h => h.2)

theorem primeNormFiber_eq_primesOver_of_split (p : ℕ) (hp : p.Prime)
    (hsplit : RationalPrimeSplitsCompletely K p) :
    primeNormFiber K p = (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P
  constructor
  · rintro ⟨hprime, hnorm⟩
    have := hprime
    exact ⟨hprime, ((arithmeticSupply_prime_norm_iff_degree_one K p hp P).mp hnorm).1⟩
  · rintro ⟨hprime, hlies⟩
    have := hprime
    have := hlies
    exact ⟨hprime, arithmeticSupply_degree_one_prime_norm K p P
      (hsplit P hprime hlies).2⟩

/-- Every unramified rational-prime norm fiber has exactly `[K:ℚ]`
members when `p` splits completely, and zero members otherwise. -/
theorem primeNormFiber_card [IsGalois ℚ K] (p : ℕ) (hp : p.Prime)
    (hunram : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    (primeNormFiber K p).ncard =
      if RationalPrimeSplitsCompletely K p then Module.finrank ℚ K else 0 := by
  classical
  by_cases hsplit : RationalPrimeSplitsCompletely K p
  · rw [ite_eq_left hsplit, primeNormFiber_eq_primesOver_of_split K p hp hsplit]
    exact arithmeticSupply_splitting_prime_fiber_card K p hp hsplit
  · rw [ite_eq_right hsplit]
    have hempty : primeNormFiber K p = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro P hP
      exact hsplit ((arithmeticSupply_degree_one_iff_splits_completely K p hp hunram).mp
        ⟨P, hP.1, hP.2⟩)
    simp only [hempty, Set.ncard_empty]

/-- Actual unramified rational primes at or below an integer endpoint. -/
def unramifiedRationalPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun p => p.Prime ∧
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}))

omit [NumberField K] in
@[simp] theorem mem_unramifiedRationalPrimes (n p : ℕ) :
    p ∈ unramifiedRationalPrimes K n ↔ p ≤ n ∧ p.Prime ∧
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  classical
  simp only [unramifiedRationalPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- Actual prime ideals with prime absolute norm at or below `n`, after
excluding the primes ramified in `K/ℚ`. -/
def unramifiedDegreeOnePrimeIdeals (n : ℕ) : Finset (Ideal (𝓞 K)) := by
  classical
  exact (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter (fun P =>
    P.IsPrime ∧ (Ideal.absNorm P).Prime ∧
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {((Ideal.absNorm P : ℕ) : ℤ)}))

@[simp] theorem mem_unramifiedDegreeOnePrimeIdeals (n : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ unramifiedDegreeOnePrimeIdeals K n ↔
      Ideal.absNorm P ≤ n ∧ P.IsPrime ∧ (Ideal.absNorm P).Prime ∧
        Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {((Ideal.absNorm P : ℕ) : ℤ)}) := by
  classical
  simp [unramifiedDegreeOnePrimeIdeals]

/-- Exact counting bridge between genuine degree-one prime ideals and
genuine unramified completely split rational primes. It holds for every
finite Galois number field, with no asymptotic premise. -/
theorem unramifiedDegreeOnePrimeIdeals_card [IsGalois ℚ K] (n : ℕ) :
    (unramifiedDegreeOnePrimeIdeals K n).card = Module.finrank ℚ K *
      ((unramifiedRationalPrimes K n).filter
        (RationalPrimeSplitsCompletely K)).card := by
  classical
  have hmaps : (unramifiedDegreeOnePrimeIdeals K n : Set (Ideal (𝓞 K))).MapsTo
      Ideal.absNorm (unramifiedRationalPrimes K n) := by
    intro P hP
    obtain ⟨hle, hprime, hnormprime, hunram⟩ :=
      (mem_unramifiedDegreeOnePrimeIdeals K n P).mp hP
    exact (mem_unramifiedRationalPrimes K n _).mpr ⟨hle, hnormprime, hunram⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (p : ℕ) (hp : p ∈ unramifiedRationalPrimes K n) :
      ((unramifiedDegreeOnePrimeIdeals K n).filter (fun P => Ideal.absNorm P = p)).card =
        if RationalPrimeSplitsCompletely K p then Module.finrank ℚ K else 0 := by
    obtain ⟨hle, hprime, hunram⟩ := (mem_unramifiedRationalPrimes K n p).mp hp
    have heq : (unramifiedDegreeOnePrimeIdeals K n).filter
        (fun P => Ideal.absNorm P = p) = (primeNormFiber_finite K p).toFinset := by
      ext P
      simp only [Finset.mem_filter, mem_unramifiedDegreeOnePrimeIdeals,
        Set.Finite.mem_toFinset, primeNormFiber, Set.mem_ofPred_eq]
      constructor
      · exact fun h => ⟨h.1.2.1, h.2⟩
      · rintro ⟨hP, hnorm⟩
        exact ⟨⟨hnorm ▸ hle, hP, hnorm ▸ hprime, hnorm ▸ hunram⟩, hnorm⟩
    rw [heq, ← Set.ncard_eq_toFinset_card (primeNormFiber K p) (primeNormFiber_finite K p)]
    exact primeNormFiber_card K p hprime hunram
  rw [Finset.sum_congr rfl hfiber]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]

end

end Entry002
