import ContinuumRemainder.FinalProof
open Set MeasureTheory
set_option autoImplicit false
example : ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set ℝ),
    (∀ l, A l ⊆ Ioi 0 ∧ ContinuumRemainder.LogSyndetic (A l)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧
      (∀ x : ℝ, x+1 ∈ E ↔ x ∈ E) ∧
      (∀ x : ℝ, ENNReal.ofReal (1-ε) < volume (E ∩ Icc x (x+1))) ∧
      ∀ l : ι, ∀ (s α y c M : ℝ) (f : ℝ → ℝ),
        0<s → 0<α → c≠0 → 0≤M →
        (∃ δ : ℝ,0<δ ∧ ∀ a∈A l,0<a → a<δ →
          |f a-y-c*a^s|≤M*a^(s+α)) →
        ∀ ρ : ℝ,0<ρ →
          ({z | ∃ a∈A l,0<a ∧ a<ρ ∧ f a=z ∧ z∉E}:Set ℝ).Infinite := by
  simpa only [ContinuumRemainder.ContinuumPowerTarget,
    ContinuumGeometric.OnePeriodic,ContinuumRemainder.AvoidsPowerRemainderTails,
    ContinuumRemainder.PowerRemainderOn,ContinuumRemainder.TailValuesOutside]
    using ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.compact_power_avoidance
