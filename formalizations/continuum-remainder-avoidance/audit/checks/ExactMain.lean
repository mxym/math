import ContinuumRemainder

set_option autoImplicit false

-- No variables, axioms, local instances, or construction hypotheses.
example : ContinuumRemainder.ContinuumPowerTarget :=
  ContinuumRemainder.continuum_power_target

-- Every project-specific predicate is expanded, including the logarithmic
-- configuration hypothesis and dyadic bins. Ordinary real mathlib instances.
example : ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set Real),
  (∀ l, A l ⊆ Set.Ioi 0 ∧
    ∃ G J : Nat, 0 < G ∧ 0 < J ∧ ∀ j : Nat, J ≤ j →
      ∃ i : Nat, j ≤ i ∧ i < j + G ∧
        (A l ∩ Set.Ioc ((1/2 : Real)^(i+1)) ((1/2 : Real)^i)).Nonempty) →
  ∀ ε : Real, 0 < ε → ε < 1 →
  ∃ E : Set Real, IsClosed E ∧ interior E = ∅ ∧
    (∀ x : Real, x+1 ∈ E ↔ x ∈ E) ∧
    (∀ x : Real, ENNReal.ofReal (1-ε) < MeasureTheory.volume (E ∩ Set.Icc x (x+1))) ∧
    ∀ l : ι, ∀ (s α y c M : Real) (f : Real → Real),
      0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
      (∃ δ : Real, 0 < δ ∧ ∀ a ∈ A l, 0 < a → a < δ →
        |f a-y-c*a^s| ≤ M*a^(s+α)) →
      ∀ ρ : Real, 0 < ρ →
        ({z : Real | ∃ a ∈ A l, 0 < a ∧ a < ρ ∧ f a=z ∧ z∉E}).Infinite :=
  ContinuumRemainder.continuum_power_target

example (u v : Real) : MeasureTheory.volume (Set.Icc u v) = ENNReal.ofReal (v-u) :=
  Real.volume_Icc
example : MeasureTheory.volume (Set.Icc (0 : Real) 1) = 1 := by norm_num

set_option pp.all true in
#print ContinuumRemainder.ContinuumPowerTarget
set_option pp.all true in
#print ContinuumRemainder.LogSyndetic
set_option pp.all true in
#print ContinuumRemainder.OccupiedBin
set_option pp.all true in
#print ContinuumRemainder.PowerRemainderOn
set_option pp.all true in
#print ContinuumRemainder.TailValuesOutside
set_option pp.all true in
#check ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.robustCompactBlockerSpec_proved
#print axioms ContinuumRemainder.compact_power_avoidance
