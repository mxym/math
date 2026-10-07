import ContinuumGeometric.Target
import ContinuumGeometric.ClosedProjection
import ContinuumGeometric.BoundedGrid

/-!
Common DEFINITIONS for the three complementary continuation lanes.
These are specifications and concrete finite-table events, not axioms or
proved existence statements. MainTarget is imported unchanged.
-/
namespace ContinuumGeometric

open Set MeasureTheory

def OnePeriodic (S : Set ℝ) : Prop :=
  ∀ x : ℝ, x + 1 ∈ S ↔ x ∈ S

noncomputable def unitDensity (S : Set ℝ) : ENNReal :=
  volume (S ∩ Ico 0 1)

def CompactPowerHits (H : Set ℝ) (K : ℕ) (k : ℤ) (N : ℕ) : Prop :=
  ∀ (x : ℝ) (p : PowerParams (1 / (K : ℝ)) K),
    ∃ n : ℕ, N ≤ n ∧ powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ H

/-- OPEN shared existence obligation. It is a proposition definition only. -/
def SmallCompactBlockerSpec : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (δ : ℝ),
    0 < δ → δ < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ OnePeriodic H ∧ unitDensity H < ENNReal.ofReal δ ∧
        CompactPowerHits H K k N

structure FiniteRoutingTables (S T : Type*) where
  selectors : S → Bool
  terminals : T → Bool

def centerExposureAtom {S : Type*} (exposed : S → Option Bool) (σ : S → Bool) : Prop :=
  ∀ (s : S) (v : Bool), exposed s = some v → σ s = v

def localRoutingSuccess {S T : Type*} {m : ℕ}
    (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (ω : FiniteRoutingTables S T) (i : Fin m) : Prop :=
  ω.selectors (own i) = true ∧ ω.terminals (terminal ω.selectors i) = true

def localRoutingAllMiss {S T : Type*} {m : ℕ}
    (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (ω : FiniteRoutingTables S T) : Prop :=
  ∀ i : Fin m, ¬localRoutingSuccess own terminal ω i

/-- Address conditions that ACTUAL routing geometry must prove on a center atom.
The terminal addresses may depend on all selectors; auxiliary entries may be shared.
-/
def LocalAddressSeparation {S T : Type*} {m : ℕ}
    (exposed : S → Option Bool) (own : Fin m → S)
    (terminal : (S → Bool) → Fin m → T) : Prop :=
  Function.Injective own ∧ (∀ i : Fin m, exposed (own i) = none) ∧
    ∀ σ : S → Bool, centerExposureAtom exposed σ → Function.Injective (terminal σ)

noncomputable def periodicGridSet (N : ℕ) (cells : Finset ℤ) : Set ℝ :=
  {z | periodicGridKey N z ∈ cells}

end ContinuumGeometric
