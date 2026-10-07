import ContinuumGeometric

open Set MeasureTheory ContinuumGeometric

-- The coefficient exclusion is mathematically necessary at any member of E.
example (E : Set Real) (b : Real) (hb : b ∈ E) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ (0 : Real) * (1 / 2) ^ n + b ∉ E) := by
  intro h
  obtain ⟨n, _, hn⟩ := h 0
  simp only [zero_mul, zero_add] at hn
  exact hn hb

-- q = 0 cannot be silently admitted: every tail after the first is constant.
example (E : Set Real) (a b : Real) (hb : b ∈ E) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a * (0 : Real) ^ n + b ∉ E) := by
  intro h
  obtain ⟨n, hn, hmiss⟩ := h 1
  have hne : n ≠ 0 := by omega
  simp only [zero_pow hne, mul_zero, zero_add] at hmiss
  exact hmiss hb

-- q = 1 also makes a constant sequence.
example (E : Set Real) (a b : Real) (hb : a + b ∈ E) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a * (1 : Real) ^ n + b ∉ E) := by
  intro h
  obtain ⟨n, _, hmiss⟩ := h 0
  simp only [one_pow, mul_one] at hmiss
  exact hmiss hb

-- The compact set cannot simply be the whole unit interval.
example : ¬ AvoidsGeometricTails (Icc (0 : Real) 1) := by
  intro h
  obtain ⟨n, _, hn⟩ := h 1 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0
  apply hn
  simp only [one_mul, add_zero, mem_Icc]
  exact ⟨pow_nonneg (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

-- Strict measure is enough for a nonempty genuine real compact set.
example : ∃ E : Set Real, IsCompact E ∧ E.Nonempty ∧ AvoidsGeometricTails E := by
  obtain ⟨E, hc, _, hv, ha⟩ := geometric_main_target (1 / 2) (by norm_num) (by norm_num)
  refine ⟨E, hc, ?_, ha⟩
  by_contra h
  have : E = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [this] at hv
