import ArithmeticSupplyWeakFromDirichlet
import Entry002.WeakCoreWeakTargets
import Entry002.WeakAssembly

/-! The literal all-quadratic-order target is reduced to one displayed
prime-specific Dirichlet-to-good-bin implication. The actual weak principal
supply is proved by ray fields and finite normal closures; no natural prime
counting asymptotic is assumed. -/
set_option autoImplicit false

namespace Entry002

/-- The unchanged literal target follows from the single remaining analytic
bridge for sets consisting of actual rational primes. -/
theorem arithmeticSupply_mainTarget_of_prime_dirichlet_good_bin_bridge
    (hbridge : ∀ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) →
      PositiveUpperDirichletSupply P → PositiveUpperLogGoodBinSupply P) :
    MainTarget :=
  mainTarget_of_weak_supply_and_weak_finiteSieve
    arithmeticSupply_weakPrincipalSupply_from_Dirichlet
    (WeakA5.weakFiniteSieveTarget_of_prime_dirichlet_good_bin_bridge hbridge)

end Entry002
