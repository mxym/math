import ArithmeticSupplyRayConductor
import Entry002.ArithmeticPrincipalSupplyAssembly
import Entry002.ArithmeticSplittingTower
import Entry002.ArithmeticSplittingAsymptotics
import Entry002.ArithmeticFinitePrimeExclusion

/-! The only analytic input below is the actual number-field prime-ideal
counting theorem. Ray fields, finite normal closures, splitting descent,
conductor generators, conjugate kernels, and dyadic conversion are derived. -/
set_option autoImplicit false
open scoped NumberField Topology
open NumberField IsDedekindDomain ClassFieldTheory Filter
namespace Entry002

/-- A rational prime greater than the conductor is outside the actual
principal conductor ray modulus; this is derived by lying-over membership. -/
theorem arithmeticSupply_conductor_primeTo_of_gt (K : Type)
    [Field K] [NumberField K] (f p : ℕ) (hf : 0 < f) (hpf : f < p)
    (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    v ∉ (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')).finitePart.support := by
  intro hv
  have hn := Finsupp.mem_support_iff.mp hv
  have hval : v.valuation K (f : K) < 1 := by
    rw [show (f : K) = ((f : 𝓞 K) : K) from rfl,
      integralRayModulus_valuation K (f : 𝓞 K) (by exact_mod_cast hf.ne') v,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hmem : (f : 𝓞 K) ∈ v.asIdeal :=
    (v.valuation_lt_one_iff_mem (K := K) (f : 𝓞 K)).mp hval
  have hint : (f : ℤ) ∈ Ideal.span {(p : ℤ)} :=
    (Ideal.mem_of_liesOver v.asIdeal (Ideal.span {(p : ℤ)}) (f : ℤ)).mpr (by simpa using hmem)
  have hdvd : p ∣ f := by
    exact_mod_cast (Ideal.mem_span_singleton.mp hint)
  exact (not_le_of_gt hpf) (Nat.le_of_dvd hf hdvd)

/-- The exact unchanged universal principal supply follows conditionally
from the actual number-field prime-ideal counting theorem. The sole premise
is the displayed asymptotic for genuine nonzero prime ideals in number fields. -/
theorem arithmeticSupply_principalSupply_of_primeIdealPNT
    (hPrimeIdeal : ∀ (N : Type) [Field N] [NumberField N],
      Tendsto (fun x : ℝ =>
        ((nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) / (x / Real.log x))
        atTop (nhds 1)) : PrincipalSplitPrimeSupplyTarget := by
  classical
  intro K _ _ hK f hf
  obtain ⟨R⟩ := rayClassField_reciprocity K
    (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne'))
  let L : Type := R.extension
  let N : Type := IntermediateField.normalClosure ℚ L (AlgebraicClosure L)
  letI : NumberField N := arithmeticSupply_normal_closure_numberField L
  letI : IsGalois ℚ N := arithmeticSupply_normal_closure_isGalois L
  let e : L →ₐ[ℚ] N := Classical.choice (arithmeticSupply_finite_normal_closure L).2.2
  letI : Algebra L N := e.toRingHom.toAlgebra
  letI : Algebra K N := (e.toRingHom.comp (algebraMap K L)).toAlgebra
  let ρ : ℝ := 1 / (Module.finrank ℚ N : ℝ)
  let P : Set ℕ := {p | p ∈ completelySplittingRationalPrimes N ∧ f < p}
  have hlim := arithmeticSupply_splitting_dyadic_of_prime_ideal_theorem N (hPrimeIdeal N)
  have hdensity : Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      atTop (nhds ρ) :=
    arithmeticSupply_dyadic_above_cutoff (completelySplittingRationalPrimes N) f ρ hlim.2
  have hgen : ∀ p ∈ P, ∃ (A : conductorOrder K f) (I : Ideal (𝓞 K)),
      I.IsPrime ∧ I.LiesOver (Ideal.span {(p : ℤ)}) ∧
      I.ramificationIdx ℤ = 1 ∧ I.inertiaDeg ℤ = 1 ∧
      Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = I := by
    intro p hp
    obtain ⟨v, hv, he, hd, _, hrel⟩ := arithmeticSupply_exists_normal_overfield_prime_package
      K L N p hp.1.1 hp.1.2.2
    have := hv
    have hvmod := arithmeticSupply_conductor_primeTo_of_gt K f p hf hp.2 v
    have hsplit : FinitePrimeSplitsCompletely K R.extension v := hrel
    obtain ⟨A, hspan, _⟩ := arithmeticSupply_ray_split_conductor_generator K f hf R v hvmod hsplit
    exact ⟨A, v.asIdeal, inferInstance, hv, he, hd, hspan⟩
  choose A I hI hlies he hd hspan using hgen
  let a : ℕ → conductorOrder K f := fun p => if hp : p ∈ P then A p hp else 0
  have ha : ∀ p ∈ P, ∃ I : Ideal (𝓞 K), I.IsPrime ∧
      I.LiesOver (Ideal.span {(p : ℤ)}) ∧ I.ramificationIdx ℤ = 1 ∧
      I.inertiaDeg ℤ = 1 ∧
      Ideal.span ({conductorOrderToIntegers K f (a p)} : Set (𝓞 K)) = I := by
    intro p hp
    refine ⟨I p hp, hI p hp, hlies p hp, he p hp, hd p hp, ?_⟩
    simpa only [a, dite_eq_left hp] using hspan p hp
  obtain ⟨τ, hτ⟩ := arithmeticSupply_quadratic_nonidentity_automorphism K hK
  obtain ⟨data, α, _, hnormkernel, hconj, hpair, hring, hρ, hlimit⟩ :=
    arithmeticSupply_of_principal_split_witnesses K hK f hf τ hτ P
      (fun p hp => hp.1.1) a ha ρ hlim.1 hdensity
  exact ⟨data, α, τ, hτ, hnormkernel, hconj, hpair, hring, ρ, hρ, hlimit⟩

end Entry002
