import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Literal target of entry002 v3 Theorem 1.1. Definitions are not proofs. -/
set_option autoImplicit false

open Module
namespace Entry002

/-- The actual conductor-f order ℤ + f 𝓞_K as a subring of K. -/
def conductorOrder (K : Type*) [Field K] [NumberField K] (f : ℕ) : Subring K where
  carrier := {x | ∃ n : ℤ, ∃ y : NumberField.RingOfIntegers K,
    x = (n : K) + (f : K) * (y : K)}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x z ⟨n, y, rfl⟩ ⟨m, w, rfl⟩
    refine ⟨n + m, y + w, ?_⟩
    simp only [Int.cast_add, map_add]
    ring
  neg_mem' := by
    rintro x ⟨n, y, rfl⟩
    refine ⟨-n, -y, ?_⟩
    simp only [Int.cast_neg, map_neg]
    ring
  mul_mem' := by
    rintro x z ⟨n, y, rfl⟩ ⟨m, w, rfl⟩
    refine ⟨n * m, (n : NumberField.RingOfIntegers K) * w +
      (m : NumberField.RingOfIntegers K) * y +
      (f : NumberField.RingOfIntegers K) * y * w, ?_⟩
    simp only [Int.cast_mul, map_add, map_mul, map_intCast, map_natCast]
    ring

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev CoeffSpace := Fin 2 → ℝ

/-- Restriction of a real linear coordinate isomorphism to the integral order. -/
noncomputable def planarEmbedding {O : Type*} [AddCommGroup O]
    (b : Basis (Fin 2) ℤ O) (e : CoeffSpace ≃ₗ[ℝ] Plane) (x : O) : Plane :=
  e (fun i => (b.repr x i : ℝ))

abbrev PrimeVertex (O : Type*) [CommRing O] := {x : O // Irreducible x}

noncomputable def primeGraph {O : Type*} [CommRing O]
    (b : Basis (Fin 2) ℤ O) (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) :
    SimpleGraph (PrimeVertex O) where
  Adj x y := x ≠ y ∧ ‖planarEmbedding b e x.val - planarEmbedding b e y.val‖ ≤ D
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [norm_sub_rev] using h.2⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- The literal all-quadratic-orders target. This Prop has no asserted proof. -/
def MainTarget : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (f : ℕ), 0 < f →
  ∀ (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ), 0 ≤ D →
  ∃ B : ℕ,
    (∀ x : PrimeVertex (conductorOrder K f),
      {y | (primeGraph b e D).Reachable x y}.Finite ∧
      {y | (primeGraph b e D).Reachable x y}.ncard ≤ B) ∧
    (∀ (n : ℕ) (w : Fin n → PrimeVertex (conductorOrder K f)),
      Function.Injective w →
      (∀ i j : Fin n, j.val = i.val + 1 → (primeGraph b e D).Adj (w i) (w j)) →
      n ≤ B) ∧
    (∀ w : ℕ → PrimeVertex (conductorOrder K f), Function.Injective w →
      (∀ t, (primeGraph b e D).Adj (w t) (w (t + 1))) → False)

end Entry002
