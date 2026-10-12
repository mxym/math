import ContinuumGeometric
open ContinuumGeometric Set MeasureTheory

#check smallCompactBlockerSpec_proved
#check geometric_main_target
#print axioms geometric_main_target
example : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc 0 1 ∧ ENNReal.ofReal (1 - ε) < volume E ∧ (∀ a b q : ℝ, a ≠ 0 → 0 < q → q < 1 → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∉ E) := geometric_main_target
