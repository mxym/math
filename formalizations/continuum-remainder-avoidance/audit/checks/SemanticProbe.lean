import ContinuumRemainder.FinalProof

/- Independently written semantic probes. Submitted sources remain untouched. -/
set_option autoImplicit false
open Set MeasureTheory ContinuumGeometric ContinuumRemainder

namespace IndependentSemanticReview

-- A genuinely discrete positive configuration satisfies the source hypothesis.
def dyadicConfiguration : Set ℝ := Set.range dyadic

theorem dyadicConfiguration_positive : dyadicConfiguration ⊆ Ioi (0 : ℝ) := by
  rintro a ⟨n, rfl⟩
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n

theorem dyadicConfiguration_logSyndetic : LogSyndetic dyadicConfiguration := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro j _
  refine ⟨j, le_rfl, by omega, ?_⟩
  refine ⟨dyadic j, ⟨j, rfl⟩, ?_, le_rfl⟩
  have hp : 0 < (1 / 2 : ℝ) ^ j := pow_pos (by norm_num) _
  change (1 / 2 : ℝ) ^ (j + 1) < (1 / 2 : ℝ) ^ j
  rw [pow_succ]
  nlinarith

-- Exact leading powers make the remainder condition nonvacuous for every s.
theorem exact_power_remainder (A : Set ℝ) (y c s α : ℝ) :
    PowerRemainderOn A (fun a => y + c * a ^ s) y c s α 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro a _ _ _
  have heq : y + c * a ^ s - y - c * a ^ s = 0 := by ring
  rw [heq, abs_zero, zero_mul]

-- One actual family member and an actual epsilon yield the full infinite-image
-- assertion simultaneously for the continuum of powers and both signs.
theorem nonvacuous_discrete_conclusion :
    ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧ OnePeriodic E ∧
      (∀ x : ℝ, ENNReal.ofReal (1 / 2) < volume (E ∩ Icc x (x + 1))) ∧
      ∀ s y c : ℝ, 0 < s → c ≠ 0 → ∀ ρ : ℝ, 0 < ρ →
        {z : ℝ | ∃ a ∈ dyadicConfiguration, 0 < a ∧ a < ρ ∧
          y + c * a ^ s = z ∧ z ∉ E}.Infinite := by
  obtain ⟨E, hclosed, hinterior, hperiodic, hmeasure, havoid⟩ :=
    continuum_power_target Unit (fun _ => dyadicConfiguration)
      (fun _ => ⟨dyadicConfiguration_positive, dyadicConfiguration_logSyndetic⟩)
      (1 / 2) (by norm_num) (by norm_num)
  refine ⟨E, hclosed, hinterior, hperiodic, ?_, ?_⟩
  · intro x
    convert hmeasure x using 1
    norm_num
  · intro s y c hs hc ρ hρ
    exact havoid () s 1 y c 0 (fun a => y + c * a ^ s)
      hs zero_lt_one hc le_rfl (exact_power_remainder dyadicConfiguration y c s 1) ρ hρ

-- This strengthens the supplied partial-tail probe in its surface presentation:
-- g is defined on (0, sigma), its bound need only hold eventually, and the
-- conclusion is phrased for every positive rho without requiring rho <= sigma.
theorem fully_partial_eventual_target :
    ∀ (ι : Type) [Countable ι] [Nonempty ι] (A : ι → Set ℝ),
      (∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l)) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧ OnePeriodic E ∧
          (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) ∧
          ∀ l : ι, ∀ (s α y c M σ : ℝ) (g : PositiveTail (A l) σ → ℝ),
            0 < s → 0 < α → c ≠ 0 → 0 ≤ M → 0 < σ →
            (∃ τ : ℝ, 0 < τ ∧ ∀ a : PositiveTail (A l) σ, (a : ℝ) < τ →
              |g a - y - c * (a : ℝ) ^ s| ≤ M * (a : ℝ) ^ (s + α)) →
            ∀ ρ : ℝ, 0 < ρ →
              {z : ℝ | ∃ a : PositiveTail (A l) σ,
                (a : ℝ) < ρ ∧ g a = z ∧ z ∉ E}.Infinite := by
  intro ι _ _ A hA ε hε hε₁
  obtain ⟨E, hEc, hEi, hEp, hEμ, havoid⟩ :=
    continuum_power_target ι A hA ε hε hε₁
  refine ⟨E, hEc, hEi, hEp, hEμ, ?_⟩
  intro l s α y c M σ g hs hα hc hM hσ hbound ρ hρ
  obtain ⟨τ, hτ, hbound⟩ := hbound
  have hrem : PowerRemainderOn (A l) (totalTailExtension (A l) σ g 0) y c s α M := by
    refine ⟨min σ τ, lt_min hσ hτ, ?_⟩
    intro a ha ha₀ hat
    have haσ : a < σ := hat.trans_le (min_le_left _ _)
    have haτ : a < τ := hat.trans_le (min_le_right _ _)
    rw [show totalTailExtension (A l) σ g 0 a = g ⟨a, ha, ha₀, haσ⟩ from
      totalTailExtension_apply (A l) σ g 0 ⟨a, ha, ha₀, haσ⟩]
    exact hbound ⟨a, ha, ha₀, haσ⟩ haτ
  have hi := havoid l s α y c M (totalTailExtension (A l) σ g 0)
    hs hα hc hM hrem (min ρ σ) (lt_min hρ hσ)
  rw [tailValuesOutside_totalTailExtension (A l) E σ (min ρ σ) (min_le_right _ _) g 0] at hi
  apply hi.mono
  rintro z ⟨a, ha, hga, hz⟩
  exact ⟨a, ha.trans_le (min_le_left _ _), hga, hz⟩

#print axioms dyadicConfiguration_logSyndetic
#print axioms nonvacuous_discrete_conclusion
#print axioms fully_partial_eventual_target

end IndependentSemanticReview
