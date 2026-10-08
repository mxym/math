import Entry002.WeakSupplyInterfaces
import Entry002.Orders

/-! The distinct all-order weak principal supply target. It retains every
non-density witness of PrincipalSplitPrimeSupplyTarget. This open proposition
does not assert the old natural dyadic density or the original MainTarget. -/
set_option autoImplicit false
namespace Entry002

/-- Actual principal kernels, conjugate norm-prime generators, paired pO,
unital residue maps, and positive upper Dirichlet supply for every conductor. -/
def WeakPrincipalSplitPrimeSupplyTarget : Prop :=
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
    PositiveUpperDirichletSupply data.primes

end Entry002
