import ContinuumRemainder.Specification
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Distinctness is a consequence of the nonzero leading coefficient, rather than
of choosing many input points.  No regularity of the remainder function is used.
-/
namespace ContinuumRemainder

open Set MeasureTheory Filter Topology

/-- Positive powers become arbitrarily small on a positive real tail. -/
theorem positive_power_small (s B : ℝ) (hs : 0 < s) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a < δ → a ^ s < B := by
  have hc := (Real.continuous_rpow_const hs.le).continuousAt (x := (0 : ℝ))
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.1 hc B hB
  refine ⟨δ, hδ, ?_⟩
  intro a ha haδ
  have hb : dist (a ^ s) ((0 : ℝ) ^ s) < B :=
    hnear (by simpa [Real.dist_eq, abs_of_pos ha] using haδ)
  simpa [Real.zero_rpow hs.ne', Real.dist_eq,
    abs_of_pos (Real.rpow_pos_of_pos ha s)] using hb

/-- The leading power bounds the image away from its center on a small tail.
Both bounds are quantitative and the lower one is strictly positive. -/
theorem powerRemainder_two_sided {A : Set ℝ} {f : ℝ → ℝ} {y c s α M : ℝ}
    (_hs : 0 < s) (hα : 0 < α) (hc : c ≠ 0) (hM : 0 ≤ M)
    (hf : PowerRemainderOn A f y c s α M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ A, 0 < a → a < δ →
      0 < (|c| / 2) * a ^ s ∧
      (|c| / 2) * a ^ s ≤ |f a - y| ∧
      |f a - y| ≤ (3 * |c| / 2) * a ^ s := by
  obtain ⟨ρ, hρ, hrem⟩ := hf
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hB : 0 < |c| / (2 * (M + 1)) := by positivity
  obtain ⟨η, hη, hsmall⟩ := positive_power_small α _ hα hB
  refine ⟨min ρ η, lt_min hρ hη, ?_⟩
  intro a ha ha₀ haδ
  have has : 0 < a ^ s := Real.rpow_pos_of_pos ha₀ s
  have haa : 0 < a ^ α := Real.rpow_pos_of_pos ha₀ α
  have hsmall' := hsmall a ha₀ (haδ.trans_le (min_le_right _ _))
  have hmul : M * a ^ α ≤ |c| / 2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * (M + 1))).1 hsmall'
    nlinarith
  have he : |f a - y - c * a ^ s| ≤ (|c| / 2) * a ^ s := by
    calc
      |f a - y - c * a ^ s| ≤ M * a ^ (s + α) :=
        hrem a ha ha₀ (haδ.trans_le (min_le_left _ _))
      _ = (M * a ^ α) * a ^ s := by rw [Real.rpow_add ha₀]; ring
      _ ≤ (|c| / 2) * a ^ s := mul_le_mul_of_nonneg_right hmul has.le
  have hlow := abs_sub (f a - y) (f a - y - c * a ^ s)
  have hsub : f a - y - (f a - y - c * a ^ s) = c * a ^ s := by ring
  rw [hsub, abs_mul, abs_of_pos has] at hlow
  have hupp := abs_add_le (c * a ^ s) (f a - y - c * a ^ s)
  have hadd : c * a ^ s + (f a - y - c * a ^ s) = f a - y := by ring
  rw [hadd, abs_mul, abs_of_pos has] at hupp
  refine ⟨mul_pos (by positivity) has, ?_, ?_⟩ <;> nlinarith

/-- A set containing noncentral points arbitrarily close to a center is infinite. -/
theorem infinite_of_arbitrarily_close_ne (S : Set ℝ) (y : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ z ∈ S, z ≠ y ∧ |z - y| < η) : S.Infinite := by
  intro hfinite
  have hclosed : IsClosed (S \ {y}) := (hfinite.subset sdiff_subset).isClosed
  have hy : y ∈ closure (S \ {y}) := by
    apply Metric.mem_closure_iff.2
    intro η hη
    obtain ⟨z, hz, hzy, hdist⟩ := h η hη
    refine ⟨z, ⟨hz, by simpa using hzy⟩, ?_⟩
    simpa [Real.dist_eq, abs_sub_comm] using hdist
  rw [hclosed.closure_eq] at hy
  exact hy.2 (mem_singleton y)

/-- One hit in every input tail yields infinitely many DISTINCT image misses
in every requested tail.  The nonzero leading power excludes the center. -/
theorem infinite_tailValuesOutside_of_hits {A E : Set ℝ} {f : ℝ → ℝ}
    {y c s α M : ℝ} (hs : 0 < s) (hα : 0 < α) (hc : c ≠ 0) (hM : 0 ≤ M)
    (hf : PowerRemainderOn A f y c s α M)
    (hhit : ∀ δ : ℝ, 0 < δ → ∃ a ∈ A, 0 < a ∧ a < δ ∧ f a ∉ E)
    (ρ : ℝ) (hρ : 0 < ρ) : (TailValuesOutside A f E ρ).Infinite := by
  obtain ⟨δ, hδ, hbound⟩ := powerRemainder_two_sided hs hα hc hM hf
  apply infinite_of_arbitrarily_close_ne _ y
  intro η hη
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hC : 0 < 3 * |c| / 2 := by positivity
  obtain ⟨τ, hτ, hsmall⟩ := positive_power_small s (η / (3 * |c| / 2)) hs
    (div_pos hη hC)
  obtain ⟨a, ha, ha₀, hatail, hamiss⟩ := hhit (min ρ (min δ τ))
    (lt_min hρ (lt_min hδ hτ))
  have haρ : a < ρ := hatail.trans_le (min_le_left _ _)
  have haδ : a < δ := hatail.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haτ : a < τ := hatail.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpositive, hlower, hupper⟩ := hbound a ha ha₀ haδ
  refine ⟨f a, ⟨a, ha, ha₀, haρ, rfl, hamiss⟩, ?_, ?_⟩
  · intro heq
    simp only [heq, sub_self, abs_zero] at hlower
    exact (not_le_of_gt hpositive) hlower
  · have := (lt_div_iff₀ hC).1 (hsmall a ha₀ haτ)
    nlinarith

/-- The domain of an actually tail-defined map. -/
abbrev PositiveTail (A : Set ℝ) (σ : ℝ) :=
  {a : ℝ // a ∈ A ∧ 0 < a ∧ a < σ}

/-- Extending a tail-defined map adds no hypotheses about its regularity. -/
noncomputable def totalTailExtension (A : Set ℝ) (σ : ℝ)
    (g : PositiveTail A σ → ℝ) (default : ℝ) : ℝ → ℝ := by
  classical
  exact fun a => if ha : a ∈ A ∧ 0 < a ∧ a < σ then g ⟨a, ha⟩ else default

@[simp] theorem totalTailExtension_apply (A : Set ℝ) (σ : ℝ)
    (g : PositiveTail A σ → ℝ) (default : ℝ) (a : PositiveTail A σ) :
    totalTailExtension A σ g default a = g a := by
  classical
  simp [totalTailExtension, a.property]

/-- A bound on the partial tail becomes exactly the same bound for its total
extension; values outside the stated tail are irrelevant. -/
theorem powerRemainderOn_totalTailExtension (A : Set ℝ) (σ : ℝ) (hσ : 0 < σ)
    (g : PositiveTail A σ → ℝ) (default y c s α M : ℝ)
    (hg : ∀ a : PositiveTail A σ,
      |g a - y - c * (a : ℝ) ^ s| ≤ M * (a : ℝ) ^ (s + α)) :
    PowerRemainderOn A (totalTailExtension A σ g default) y c s α M := by
  refine ⟨σ, hσ, ?_⟩
  intro a ha ha₀ haσ
  rw [show totalTailExtension A σ g default a = g ⟨a, ha, ha₀, haσ⟩ from
    totalTailExtension_apply A σ g default ⟨a, ha, ha₀, haσ⟩]
  exact hg ⟨a, ha, ha₀, haσ⟩

/-- On every smaller tail the total extension has exactly the partial map's
missed values, so its infinite-distinct-values conclusion is equivalent. -/
theorem tailValuesOutside_totalTailExtension (A E : Set ℝ) (σ ρ : ℝ) (hρσ : ρ ≤ σ)
    (g : PositiveTail A σ → ℝ) (default : ℝ) :
    TailValuesOutside A (totalTailExtension A σ g default) E ρ =
      {z | ∃ a : PositiveTail A σ, (a : ℝ) < ρ ∧ g a = z ∧ z ∉ E} := by
  ext z
  constructor
  · rintro ⟨a, ha, ha₀, haρ, hga, hz⟩
    let a' : PositiveTail A σ := ⟨a, ha, ha₀, haρ.trans_le hρσ⟩
    refine ⟨a', haρ, ?_, hz⟩
    simpa only [← totalTailExtension_apply A σ g default a'] using hga
  · rintro ⟨a, haρ, hga, hz⟩
    exact ⟨a, a.property.1, a.property.2.1, haρ,
      by simpa only [totalTailExtension_apply] using hga, hz⟩

end ContinuumRemainder
