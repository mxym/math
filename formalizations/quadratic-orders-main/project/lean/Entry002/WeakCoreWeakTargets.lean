import Entry002.WeakCoreGoodBinFiniteSieve
import Entry002.WeakSieveTargets

/-! Exact weak-target corollaries. The prime-restricted analytic implication
is a displayed premise, so neither target is claimed unconditionally here.
The actual finite component bound and actual avoiding walks are used verbatim;
no former A5 field or strong arithmetic endpoint is introduced. -/
set_option autoImplicit false
namespace Entry002.WeakA5

/-- The literal weak finite-sieve target follows from the proved core plus
logarithmic good-bin engine and an explicit prime-restricted analytic bridge. -/
theorem weakFiniteSieveTarget_of_prime_dirichlet_good_bin_bridge
    (hbridge : ∀ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) →
      PositiveUpperDirichletSupply P → PositiveUpperLogGoodBinSupply P) :
    WeakFiniteSieveTarget := by
  intro L _ b e data A
  exact core_finite_sieve_of_log_good_bins A.core
    (hbridge data.primes data.prime_mem A.upper_dirichlet_supply)

/-- Finite actual components prohibit every infinite injective avoiding walk.
The selected prime pool still precedes all walk quantifiers. -/
theorem weakFiniteSieveNoWalkTarget_of_finiteSieveTarget
    (hfinite : WeakFiniteSieveTarget) : WeakFiniteSieveNoWalkTarget := by
  intro L _ b e data A D hD
  obtain ⟨S, hS, hbound⟩ := hfinite L b e data A D hD
  refine ⟨S, hS, ?_⟩
  intro z hz havoid hstep
  let w : ℕ → avoiding data S := fun n => ⟨z n, havoid n⟩
  have hw : Function.Injective w := by
    intro i j hij
    exact hz (congrArg Subtype.val hij)
  apply no_infinite_injective_walk (latticeGraph b e D (avoiding data S)) hbound w ?_ hw
  intro n
  refine ⟨?_, ?_⟩
  · exact fun h => (show n ≠ n+1 by omega) (hw h)
  · simpa only [dist_eq_norm] using hstep n

/-- The exact weak no-walk target, conditional on the same single displayed
prime-specific analytic bridge. -/
theorem weakFiniteSieveNoWalkTarget_of_prime_dirichlet_good_bin_bridge
    (hbridge : ∀ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) →
      PositiveUpperDirichletSupply P → PositiveUpperLogGoodBinSupply P) :
    WeakFiniteSieveNoWalkTarget :=
  weakFiniteSieveNoWalkTarget_of_finiteSieveTarget
    (weakFiniteSieveTarget_of_prime_dirichlet_good_bin_bridge hbridge)

end Entry002.WeakA5
