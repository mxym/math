import Entry002.ArithmeticConductorConjugation
import Entry002.ArithmeticInterface

/-! Explicit assembly from genuine actual prime ideals and a supplied natural
counting limit. The generator and density hypotheses remain visible. -/
set_option autoImplicit false
namespace Entry002
open scoped NumberField Topology

/-- The principal supply conclusion for one actual order follows from actual
unramified degree-one principal prime witnesses and the actual positive dyadic
density. Neither witness existence nor that density is inserted as an axiom. -/
theorem arithmeticSupply_of_principal_split_witnesses
    (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (f : ℕ) (hf : 0 < f)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (P : Set ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℕ → conductorOrder K f)
    (hgen : ∀ p ∈ P, ∃ I : Ideal (𝓞 K), I.IsPrime ∧
      I.LiesOver (Ideal.span {(p : ℤ)}) ∧ I.ramificationIdx ℤ = 1 ∧
      I.inertiaDeg ℤ = 1 ∧
      Ideal.span ({conductorOrderToIntegers K f (a p)} : Set (𝓞 K)) = I)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hdensity : Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ)) :
    ∃ (data : SignedResidueData (conductorOrder K f))
      (α : ℕ → Bool → conductorOrder K f),
      data.primes = P ∧
      (∀ p ∈ data.primes, ∀ s : Bool,
        (Algebra.norm ℤ (α p s)).natAbs = p ∧
        ∀ x : conductorOrder K f, data.phi p s x = 0 ↔ α p s ∣ x) ∧
      (∀ p ∈ data.primes, ((α p false : conductorOrder K f) : K) =
        τ ((α p true : conductorOrder K f) : K)) ∧
      (∀ p ∈ data.primes, ∀ x : conductorOrder K f,
        (data.phi p true x = 0 ∧ data.phi p false x = 0) ↔
          ∃ y : conductorOrder K f, x = (p : ℤ) • y) ∧
      (∀ p ∈ data.primes, ∀ s : Bool,
        ∃ ψ : conductorOrder K f →+* ZMod p, ψ.toAddMonoidHom = data.phi p s) ∧
      0 < ρ ∧ Filter.Tendsto
        (fun T : ℝ => (dyadicPrimeCount data.primes T : ℝ) / (T / Real.log T))
        Filter.atTop (nhds ρ) := by
  classical
  have H (p : ℕ) (hp : p ∈ P) :
      (Algebra.norm ℤ (a p)).natAbs = p ∧
      (Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ (a p))).natAbs = p ∧
      ∃ ψT ψF : conductorOrder K f →+* ZMod p,
        Function.Surjective ψT ∧ Function.Surjective ψF ∧
        (∀ x, ψT x = 0 ↔ a p ∣ x) ∧
        (∀ x, ψF x = 0 ↔ arithmeticSupply_conductorAutomorphism K f τ (a p) ∣ x) ∧
        ∀ x, (ψT x = 0 ∧ ψF x = 0) ↔ ∃ y, x = (p : ℤ) • y := by
    obtain ⟨I, hI, hIp, he, hd, hspan⟩ := hgen p hp
    have := hI
    have := hIp
    exact arithmeticSupply_split_conductor_residue_pair K f hK hf τ hτ
      p (hprime p hp) I he hd (a p) hspan
  have hn (p : ℕ) (hp : p ∈ P) := (H p hp).1
  have hnb (p : ℕ) (hp : p ∈ P) := (H p hp).2.1
  have hm (p : ℕ) (hp : p ∈ P) := (H p hp).2.2
  choose ψT ψF hT hF hKT hKF hpair using hm
  let data : SignedResidueData (conductorOrder K f) := {
    primes := P
    prime_mem := hprime
    phi := fun p s => if hp : p ∈ P then
      (if s then ψT p hp else ψF p hp).toAddMonoidHom else 0
    onto := by
      intro p hp s
      simp only [dite_eq_left hp]
      cases s
      · exact hF p hp
      · exact hT p hp }
  let α : ℕ → Bool → conductorOrder K f := fun p s =>
    if s then a p else arithmeticSupply_conductorAutomorphism K f τ (a p)
  refine ⟨data, α, rfl, ?_, ?_, ?_, ?_, hρ, hdensity⟩
  · intro p hp s
    change p ∈ P at hp
    cases s
    · exact ⟨hnb p hp, by simpa [data, α, hp] using hKF p hp⟩
    · exact ⟨hn p hp, by simpa [data, α, hp] using hKT p hp⟩
  · intro p hp
    exact rfl
  · intro p hp x
    change p ∈ P at hp
    simpa [data, hp] using hpair p hp x
  · intro p hp s
    change p ∈ P at hp
    refine ⟨if s then ψT p hp else ψF p hp, ?_⟩
    simp only [data, dite_eq_left hp]

/-- The complete actual A1–A5 interface follows for every integral basis
and planar realization from the same explicit arithmetic witnesses and density. -/
theorem arithmeticSupply_interface_of_principal_split_witnesses
    (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (f : ℕ) (hf : 0 < f)
    (P : Set ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℕ → conductorOrder K f)
    (hgen : ∀ p ∈ P, ∃ I : Ideal (𝓞 K), I.IsPrime ∧
      I.LiesOver (Ideal.span {(p : ℤ)}) ∧ I.ramificationIdx ℤ = 1 ∧
      I.inertiaDeg ℤ = 1 ∧
      Ideal.span ({conductorOrderToIntegers K f (a p)} : Set (𝓞 K)) = I)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hdensity : Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ))
    (b : Module.Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ data : SignedResidueData (conductorOrder K f),
      data.primes = P ∧ ArithmeticInterface data b e := by
  obtain ⟨τ, hτ⟩ := arithmeticSupply_quadratic_nonidentity_automorphism K hK
  obtain ⟨data, α, hP, hnk, _, hpair, _, hρ', hlim⟩ :=
    arithmeticSupply_of_principal_split_witnesses K hK f hf τ hτ P hprime a hgen ρ hρ hdensity
  refine ⟨data, hP, ?_⟩
  exact order_interface_of_principal_residues K f hK hf b e data α
    (fun p hp s => (hnk p hp s).1) (fun p hp s => (hnk p hp s).2)
    hpair ⟨ρ, hρ', hlim⟩

end Entry002
