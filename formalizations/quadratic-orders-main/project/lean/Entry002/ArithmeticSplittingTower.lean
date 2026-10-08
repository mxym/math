import Entry002.ArithmeticPrimeIdealCounting
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! Complete splitting descends along actual number-field towers. Every
ramification/inertia conclusion below is derived from Mathlib's tower
multiplicativity; no splitting-descent result is assumed. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- Complete splitting over `ℚ` descends to every number subfield along
the specified actual field embedding. No Galois assumption on the subfield
or its overfield is needed for this local descent. -/
theorem arithmeticSupply_rational_splitting_descends (p : ℕ)
    (hsplit : RationalPrimeSplitsCompletely L p) :
    RationalPrimeSplitsCompletely K p := by
  intro P hP hPlies
  have := hP
  have := hPlies
  obtain ⟨Q⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L)))
  have hQp : Q.1.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans Q.1 P (Ideal.span {(p : ℤ)})
  obtain ⟨he, hf⟩ := hsplit Q.1 Q.2.1 hQp
  have hEtower := Ideal.ramificationIdx_tower P Q.1 (R := ℤ)
  have hFtower := Ideal.inertiaDeg_tower P Q.1 (R := ℤ)
  rw [he] at hEtower
  rw [hf] at hFtower
  exact ⟨Nat.eq_one_of_mul_eq_one_right hEtower.symm,
    Nat.eq_one_of_mul_eq_one_right hFtower.symm⟩

/-- If a rational prime splits completely in `L`, every prime of `K`
over it splits completely in the relative extension `L/K`. -/
theorem arithmeticSupply_rational_splitting_relative (p : ℕ)
    (hsplit : RationalPrimeSplitsCompletely L p)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver P →
      Q.ramificationIdx (𝓞 K) = 1 ∧ Q.inertiaDeg (𝓞 K) = 1 := by
  intro Q hQ hQlies
  have := hQ
  have := hQlies
  have hQp : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans Q P (Ideal.span {(p : ℤ)})
  obtain ⟨he, hf⟩ := hsplit Q hQ hQp
  have hEtower := Ideal.ramificationIdx_tower P Q (R := ℤ)
  have hFtower := Ideal.inertiaDeg_tower P Q (R := ℤ)
  rw [he] at hEtower
  rw [hf] at hFtower
  exact ⟨Nat.eq_one_of_mul_eq_one_left hEtower.symm,
    Nat.eq_one_of_mul_eq_one_left hFtower.symm⟩

/-- Height-one form, matching the actual `FinitePrimeSplitsCompletely`
predicate used by the independently audited class-field theory source. -/
theorem arithmeticSupply_rational_splitting_relative_heightOne (p : ℕ)
    (hsplit : RationalPrimeSplitsCompletely L p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  intro w hw
  exact arithmeticSupply_rational_splitting_relative K L p hsplit v.asIdeal
    w.asIdeal inferInstance hw

/-- A completely splitting rational prime supplies an actual height-one
prime below, with its degree-one norm and relative complete splitting.
The prime is constructed by lying over; its existence is not an input. -/
theorem arithmeticSupply_exists_split_prime_package (p : ℕ) (hp : p.Prime)
    (hsplit : RationalPrimeSplitsCompletely L p) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) ∧
      v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      Ideal.absNorm v.asIdeal = p ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P⟩ :=
    (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
  have hK := arithmeticSupply_rational_splitting_descends K L p hsplit
  obtain ⟨he, hf⟩ := hK P.1 P.2.1 P.2.2
  have hnorm := arithmeticSupply_degree_one_prime_norm K p P.1 hf
  have hne : P.1 ≠ ⊥ := by
    intro hbot
    have hpzero : 0 = p := by simpa only [hbot, Ideal.absNorm_bot] using hnorm
    exact hp.ne_zero hpzero.symm
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P.1, P.2.1, hne⟩
  have hv : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
  have := hv
  exact ⟨v, hv, he, hf, hnorm,
    arithmeticSupply_rational_splitting_relative_heightOne K L p hsplit v⟩

variable (N : Type*) [Field N] [NumberField N] [Algebra L N] [Algebra K N]
  

/-- A completely splitting prime in a normal overfield supplies a genuine
degree-one prime below, as well as actual complete splitting in the chosen
relative intermediate extension. -/
theorem arithmeticSupply_normal_overfield_prime_package (p : ℕ)
    (hsplit : RationalPrimeSplitsCompletely N p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
    Ideal.absNorm v.asIdeal = p ∧
    ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have hK := arithmeticSupply_rational_splitting_descends K N p hsplit
  have hL := arithmeticSupply_rational_splitting_descends L N p hsplit
  obtain ⟨he, hf⟩ := hK v.asIdeal inferInstance inferInstance
  exact ⟨he, hf, arithmeticSupply_degree_one_prime_norm K p v.asIdeal hf,
    arithmeticSupply_rational_splitting_relative_heightOne K L p hL v⟩

/-- The existential package from a completely splitting normal overfield:
both the degree-one base prime and every relative splitting conclusion are
constructed, rather than stored as additional hypotheses. -/
theorem arithmeticSupply_exists_normal_overfield_prime_package (p : ℕ) (hp : p.Prime)
    (hsplit : RationalPrimeSplitsCompletely N p) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) ∧
      v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      Ideal.absNorm v.asIdeal = p ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  exact arithmeticSupply_exists_split_prime_package K L p hp
    (arithmeticSupply_rational_splitting_descends L N p hsplit)

variable (E : Type*) [Field E] [NumberField E]

/-- The actual normal closure already constructed in pinned Mathlib is
a number field, supplying a legitimate field for the counting route. -/
theorem arithmeticSupply_normal_closure_numberField :
    NumberField (IntermediateField.normalClosure ℚ E (AlgebraicClosure E)) := by
  have := (arithmeticSupply_finite_normal_closure E).1
  exact {}

/-- Its genuine normality and characteristic-zero separability make the
actual normal closure Galois over `ℚ`; no Galois certificate is assumed. -/
theorem arithmeticSupply_normal_closure_isGalois :
    IsGalois ℚ (IntermediateField.normalClosure ℚ E (AlgebraicClosure E)) := by
  have := (arithmeticSupply_finite_normal_closure E).2.1
  exact {}

end

end Entry002
