import ContinuumGeometric.MainProof

-- Empty-context application. No variables, axioms, or local instances precede it.
example : ContinuumGeometric.MainTarget := ContinuumGeometric.geometric_main_target

example : ∀ ε : Real, 0 < ε → ε < 1 →
    ∃ E : Set Real, IsCompact E ∧ E ⊆ Set.Icc 0 1 ∧
      ENNReal.ofReal (1 - ε) < MeasureTheory.volume E ∧
      ∀ a b q : Real, a ≠ 0 → 0 < q → q < 1 →
        ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a * q ^ n + b ∉ E :=
  ContinuumGeometric.geometric_main_target

example : ContinuumGeometric.MainTarget ↔
    (∀ ε : Real, 0 < ε → ε < 1 →
      ∃ E : Set Real, IsCompact E ∧ E ⊆ Set.Icc 0 1 ∧
        ENNReal.ofReal (1 - ε) < MeasureTheory.volume E ∧
        ∀ a b q : Real, a ≠ 0 → 0 < q → q < 1 →
          ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a * q ^ n + b ∉ E) := Iff.rfl

example : MeasureTheory.volume (Set.Icc (0 : Real) 1) = 1 := by norm_num
example (u v : Real) : MeasureTheory.volume (Set.Icc u v) =
    ENNReal.ofReal (v - u) := Real.volume_Icc

example : ∃ E : Set Real, IsCompact E ∧
    (0 : ENNReal) < MeasureTheory.volume E ∧
    ContinuumGeometric.AvoidsGeometricTails E := by
  obtain ⟨E, hE, _, hV, hA⟩ :=
    ContinuumGeometric.geometric_main_target (1 / 2) (by norm_num) (by norm_num)
  exact ⟨E, hE, lt_trans (by norm_num) hV, hA⟩

set_option pp.all true in
#print ContinuumGeometric.MainTarget
set_option pp.all true in
#print ContinuumGeometric.AvoidsGeometricTails
set_option pp.all true in
#check ContinuumGeometric.geometric_main_target
#print axioms ContinuumGeometric.geometric_main_target
#print axioms ContinuumGeometric.smallCompactBlockerSpec_proved
