import Entry002.Targets
import Entry002.Graphs
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The literal A1–A5 interface in entry002 v3 §2. No analytic theorem is assumed. -/
set_option autoImplicit false
open Module Filter
open scoped BigOperators Topology
namespace Entry002

variable {L : Type*} [AddCommGroup L]

/-- Actual additive maps onto prime residue fields; no primality surrogate. -/
structure SignedResidueData (L : Type*) [AddCommGroup L] where
  primes : Set ℕ
  prime_mem : ∀ p ∈ primes, Nat.Prime p
  phi : (p : ℕ) → Bool → L →+ ZMod p
  onto : ∀ p ∈ primes, ∀ σ, Function.Surjective (phi p σ)

/-- The manuscript's nonzero primitive lattice vectors. -/
def IsPrimitive (v : L) : Prop :=
  v ≠ 0 ∧ ∀ (a : ℤ) (w : L), 1 < |a| → v ≠ a • w

/-- Actual finite count in [T,2T], with real endpoints. -/
noncomputable def dyadicPrimeCount (P : Set ℕ) (T : ℝ) : ℕ := by
  classical
  exact ((Finset.range (⌊2*T⌋₊ + 1)).filter
    (fun p => p ∈ P ∧ T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)).card

/-- All five actual arithmetic/geometric hypotheses, including positive
asymptotic dyadic density, and unrestricted finite prime selections. -/
structure ArithmeticInterface (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) : Prop where
  crt : ∀ (S : Finset ℕ), (∀ p ∈ S, p ∈ data.primes) → ∀ σ : ℕ → Bool,
    Function.Surjective (fun x : L => fun p : S => data.phi p.val (σ p.val) x)
  paired_kernel : ∀ p ∈ data.primes, ∀ x : L,
    (data.phi p true x = 0 ∧ data.phi p false x = 0) ↔
      ∃ y : L, x = (p : ℤ) • y
  collision : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : L,
    x ≠ 0 → data.phi p σ x = 0 →
      c * Real.sqrt (p : ℝ) ≤ ‖planarEmbedding b e x‖
  eligible_product : ∃ C : ℝ, 1 ≤ C ∧ ∀ v : L, IsPrimitive v →
    ∀ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) →
      ((S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)).prod
        (fun p => (p : ℝ))) ≤ C * ‖planarEmbedding b e v‖ ^ 2
  density : ∃ ρ : ℝ, 0 < ρ ∧
    Tendsto (fun T : ℝ => (dyadicPrimeCount data.primes T : ℝ) / (T / Real.log T))
      atTop (nhds ρ)

/-- Both zero classes are avoided at every selected prime. -/
def avoiding (data : SignedResidueData L) (S : Finset ℕ) : Set L :=
  {x | ∀ p ∈ S, data.phi p true x ≠ 0 ∧ data.phi p false x ≠ 0}

noncomputable def latticeGraph (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) (A : Set L) : SimpleGraph A where
  Adj x y := x ≠ y ∧ ‖planarEmbedding b e x.val - planarEmbedding b e y.val‖ ≤ D
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [norm_sub_rev] using h.2⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- The entire finite planar sieve theorem, an OPEN target. The Q² component
bound is explicit and no bound on irreducibles is presumed here. -/
def FiniteSieveTarget : Prop :=
  ∀ (L : Type) [AddCommGroup L]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L), ArithmeticInterface data b e →
  ∀ D : ℝ, 0 ≤ D → ∃ S : Finset ℕ,
    (∀ p ∈ S, p ∈ data.primes) ∧
    UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2)

end Entry002
