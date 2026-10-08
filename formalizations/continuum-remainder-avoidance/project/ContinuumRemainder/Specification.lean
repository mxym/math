import ContinuumGeometric.GeometricParameters
import ContinuumGeometric.RoutingInterfaces
import Mathlib.Topology.MetricSpace.Isometry

/-!
The stronger target, kept separate from the independently verified geometric
MainTarget. Definitions here assert no existence theorem or hidden premise.
The prescribed nonempty countable family occurs before the avoiding set.
-/
namespace ContinuumRemainder

open Set MeasureTheory Filter Topology

def OccupiedBin (A : Set ℝ) (j : ℕ) : Prop :=
  (A ∩ Ioc (ContinuumGeometric.dyadic (j + 1))
    (ContinuumGeometric.dyadic j)).Nonempty

def LogSyndetic (A : Set ℝ) : Prop :=
  ∃ G J : ℕ, 0 < G ∧ 0 < J ∧
    ∀ j : ℕ, J ≤ j → ∃ i : ℕ, j ≤ i ∧ i < j + G ∧ OccupiedBin A i

def PowerRemainderOn (A : Set ℝ) (f : ℝ → ℝ) (y c s α M : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ A, 0 < a → a < ρ →
    |f a - y - c * a ^ s| ≤ M * a ^ (s + α)

def TailValuesOutside (A : Set ℝ) (f : ℝ → ℝ) (E : Set ℝ) (ρ : ℝ) : Set ℝ :=
  {z | ∃ a ∈ A, 0 < a ∧ a < ρ ∧ f a = z ∧ z ∉ E}

def AvoidsPowerRemainderTails {ι : Type*} (A : ι → Set ℝ) (E : Set ℝ) : Prop :=
  ∀ l : ι, ∀ (s α y c M : ℝ) (f : ℝ → ℝ),
    0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
    PowerRemainderOn (A l) f y c s α M →
    ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside (A l) f E ρ).Infinite

def ContinuumPowerTarget : Prop :=
  ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set ℝ),
    (∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧
        ContinuumGeometric.OnePeriodic E ∧
        (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) ∧
        AvoidsPowerRemainderTails A E

def RobustCompactHits (H A : Set ℝ) (s₀ s₁ α₀ : ℝ) (k : ℤ)
    (q h : ℕ) : Prop :=
  ∀ (x s t : ℝ) (e : ℝ → ℝ),
    s ∈ Icc s₀ s₁ → t ∈ Icc 1 2 →
    (∀ a ∈ A, 0 < a → a < ContinuumGeometric.dyadic h →
      |e a| ≤ (q : ℝ) * a ^ (s + α₀)) →
    ∃ a ∈ A, 0 < a ∧ a < ContinuumGeometric.dyadic h ∧
      x + t * (2 : ℝ) ^ k * a ^ s + e a ∈ H

def RobustCompactBlockerSpec : Prop :=
  ∀ A : Set ℝ, A ⊆ Ioi 0 → LogSyndetic A →
    ∀ s₀ s₁ α₀ : ℝ, 0 < s₀ → s₀ < s₁ → 0 < α₀ →
    ∀ (k : ℤ) (q h : ℕ), 0 < q → 0 < h →
    ∀ p : ℝ, 0 < p → p < 1 / 12 →
    ∃ H : Set ℝ, IsOpen H ∧ ContinuumGeometric.OnePeriodic H ∧
      ContinuumGeometric.unitDensity H ≤ ENNReal.ofReal (6 * p) ∧
      RobustCompactHits H A s₀ s₁ α₀ k q h

end ContinuumRemainder
