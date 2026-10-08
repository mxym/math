import ContinuumRemainder.FinalProof

set_option autoImplicit false

open Set MeasureTheory ContinuumGeometric ContinuumRemainder

#print ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.robustCompactBlockerSpec_proved
#print axioms ContinuumRemainder.continuum_power_target
#print axioms ContinuumRemainder.compact_power_avoidance
#print axioms ContinuumRemainder.sampled_stable_missed_center_probability_le

/-- The exact expanded target fixes the prescribed nonempty countable family
before choosing E, then quantifies every real power and every arbitrary f. -/
example :
    ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set ℝ),
      (∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l)) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧ OnePeriodic E ∧
          (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) ∧
          ∀ l : ι, ∀ (s α y c M : ℝ) (f : ℝ → ℝ),
            0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
            (∃ σ : ℝ, 0 < σ ∧ ∀ a ∈ A l, 0 < a → a < σ →
              |f a - y - c * a ^ s| ≤ M * a ^ (s + α)) →
            ∀ ρ : ℝ, 0 < ρ →
              {z : ℝ | ∃ a ∈ A l, 0 < a ∧ a < ρ ∧ f a = z ∧ z ∉ E}.Infinite :=
  continuum_power_target

/-- The same E applies to genuinely tail-defined maps; extending such a map
does not impose any regularity, or a remainder bound outside its given tail. -/
example :
    ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set ℝ),
      (∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l)) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧ OnePeriodic E ∧
          (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) ∧
          ∀ l : ι, ∀ (s α y c M σ : ℝ) (g : PositiveTail (A l) σ → ℝ),
            0 < s → 0 < α → c ≠ 0 → 0 ≤ M → 0 < σ →
            (∀ a : PositiveTail (A l) σ,
              |g a - y - c * (a : ℝ) ^ s| ≤ M * (a : ℝ) ^ (s + α)) →
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ σ →
              {z : ℝ | ∃ a : PositiveTail (A l) σ,
                (a : ℝ) < ρ ∧ g a = z ∧ z ∉ E}.Infinite := by
  intro ι _ _ A hA ε hε hε₁
  obtain ⟨E, hEc, hEi, hEp, hEμ, havoid⟩ :=
    continuum_power_target ι A hA ε hε hε₁
  refine ⟨E, hEc, hEi, hEp, hEμ, ?_⟩
  intro l s α y c M σ g hs hα hc hM hσ hbound ρ hρ hρσ
  have hrem := powerRemainderOn_totalTailExtension (A l) σ hσ g 0 y c s α M hbound
  have hi := havoid l s α y c M (totalTailExtension (A l) σ g 0)
    hs hα hc hM hrem ρ hρ
  rw [tailValuesOutside_totalTailExtension (A l) E σ ρ hρσ g 0] at hi
  exact hi
