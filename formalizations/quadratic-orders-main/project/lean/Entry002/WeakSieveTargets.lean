import Entry002.WeakSupplyInterfaces
import Entry002.SieveReduction

/-! New intermediate targets for the weak route. They are not assertions that
the weak sieve is proved, and do not replace any original target definition. -/

namespace Entry002

/-- The original actual Q² component conclusion with A1--A4 and positive
upper Dirichlet supply. This proposition is currently open. -/
def WeakFiniteSieveTarget : Prop :=
  ∀ (L : Type) [AddCommGroup L]
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L), WeakArithmeticInterface data b e →
  ∀ D : ℝ, 0 ≤ D → ∃ S : Finset ℕ,
    (∀ p ∈ S, p ∈ data.primes) ∧
    UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2)

/-- A single finite pool precedes all walks, under the actual weaker input.
This proposition is currently open. -/
def WeakFiniteSieveNoWalkTarget : Prop :=
  ∀ (L : Type) [AddCommGroup L]
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L), WeakArithmeticInterface data b e →
  ∀ D : ℝ, 0 ≤ D → ∃ S : Finset ℕ,
    (∀ p ∈ S, p ∈ data.primes) ∧
    ∀ z : ℕ → L, Function.Injective z →
      (∀ t, z t ∈ avoiding data S) →
      (∀ t, dist (planarEmbedding b e (z t))
        (planarEmbedding b e (z (t + 1))) ≤ D) → False

end Entry002
