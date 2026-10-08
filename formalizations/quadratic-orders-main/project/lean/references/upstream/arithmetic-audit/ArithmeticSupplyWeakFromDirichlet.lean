import ArithmeticSupplyRayConductor
import Entry002.ArithmeticWeakPrincipalSupplyAssembly
import Entry002.ArithmeticSplittingTower
import Entry002.PrimeIdealSplitDirichletCutoff

/-! The universal weak principal supply follows from actual ray-class-field
reciprocity, the genuine finite normal closure, and the proved completely
splitting rational-prime Dirichlet supply. No prime-ideal counting theorem
is assumed by the endpoint. Existing exact audited CFT caches are read-only
inputs to the separate development compilation. -/
set_option autoImplicit false
open scoped NumberField Topology
open NumberField IsDedekindDomain ClassFieldTheory Filter
namespace Entry002

/-- A rational prime greater than the conductor is outside the actual
principal conductor ray modulus; this is derived by lying-over membership. -/
theorem arithmeticSupply_weak_conductor_primeTo_of_gt (K : Type)
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

/-- Every positive conductor in every quadratic number field has actual
principal norm-prime generators, conjugate kernels, paired pO, unital
residue maps, and positive upper Dirichlet supply. -/
theorem arithmeticSupply_weakPrincipalSupply_from_Dirichlet :
    WeakPrincipalSplitPrimeSupplyTarget := by
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
  let P : Set ℕ := {p | p ∈ completelySplittingRationalPrimes N ∧ f < p}
  have hdirichlet : PositiveUpperDirichletSupply P := by
    exact completelySplittingRationalPrimes_aboveCutoff_positiveUpperDirichletSupply N f
  have hgen : ∀ p ∈ P, ∃ (A : conductorOrder K f) (I : Ideal (𝓞 K)),
      I.IsPrime ∧ I.LiesOver (Ideal.span {(p : ℤ)}) ∧
      I.ramificationIdx ℤ = 1 ∧ I.inertiaDeg ℤ = 1 ∧
      Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = I := by
    intro p hp
    obtain ⟨v, hv, he, hd, _, hrel⟩ := arithmeticSupply_exists_normal_overfield_prime_package
      K L N p hp.1.1 hp.1.2.2
    have := hv
    have hvmod := arithmeticSupply_weak_conductor_primeTo_of_gt K f p hf hp.2 v
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
  obtain ⟨data, α, _, hnormkernel, hconj, hpair, hring, hdir⟩ :=
    arithmeticSupply_weak_of_principal_split_witnesses K hK f hf τ hτ P
      (fun p hp => hp.1.1) a ha hdirichlet
  exact ⟨data, α, τ, hτ, hnormkernel, hconj, hpair, hring, hdir⟩

end Entry002
