import Entry002.Sieve
import Entry002.Orders

/-! The exact principal split-prime supply in v3 §9, as an OPEN goal.
No class-field or Chebotarev theorem is inserted as an axiom. -/
set_option autoImplicit false
namespace Entry002

/-- Actual principal residue kernels, the conjugate generators, their prime
norms, paired intersection pO, and positive natural dyadic density. -/
def PrincipalSplitPrimeSupplyTarget : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ f : ℕ, 0 < f →
  ∃ (data : SignedResidueData (conductorOrder K f))
    (α : ℕ → Bool → conductorOrder K f) (τ : K ≃ₐ[ℚ] K),
    τ ≠ AlgEquiv.refl ∧
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
    ∃ ρ : ℝ, 0 < ρ ∧ Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount data.primes T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ)

end Entry002
