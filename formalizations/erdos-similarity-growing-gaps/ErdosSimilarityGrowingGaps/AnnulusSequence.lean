import ErdosSimilarityGrowingGaps.Input

namespace ErdosSimilarityGrowingGaps
open Filter Topology
set_option autoImplicit false

/-- Property W with the integer origins and actual sequential limit used in
Definition 1 of the paper. Every chosen window is late enough that both
logarithms are positive. -/
def WindowFilling (Z : LogScale) : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ (U : ℕ → ℕ) (D : ℕ → ℝ),
    Tendsto (fun j => (U j : ℝ)) atTop atTop ∧
    (∀ j, 1 < Real.log (U j : ℝ)) ∧
    (∀ j, FillsAnnulus Z (U j) R (D j)) ∧
    Tendsto (fun j => D j / Real.log (Real.log (U j : ℝ))) atTop (𝓝 0)

/-- Filled real annuli can be shrunk to integer-origin annuli. Using ratio
`2*R` before rounding is what preserves both endpoints. -/
theorem AnnularFilling.integer_witness {Z : LogScale} (hW : AnnularFilling Z)
    (R : ℕ) (hR : 2 ≤ R) (η : ℝ) (hη : 0 < η) (U₀ : ℝ) :
    ∃ (U : ℕ) (D : ℝ), U₀ ≤ (U : ℝ) ∧
      1 < Real.log (U : ℝ) ∧ FillsAnnulus Z U R D ∧
      D / Real.log (Real.log (U : ℝ)) ≤ η := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  obtain ⟨u, D, hu, hD, hsmall, hfill⟩ :=
    hW (2 * R) (by omega) η hη (max U₀ (Real.exp 2))
      ((Real.exp_pos 2).trans_le (le_max_right _ _))
  have hue : Real.exp 2 ≤ u := (le_max_right _ _).trans hu
  have hu0 : 0 < u := (Real.exp_pos 2).trans_le hue
  have hu1 : 1 < u := by
    have he : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by norm_num)
    exact he.trans_le hue
  let U := Nat.ceil u
  have hceil : u ≤ (U : ℝ) := Nat.le_ceil u
  have hceil_upper : (U : ℝ) ≤ 2 * u := by
    have := Nat.ceil_lt_add_one hu0.le
    dsimp [U]
    linarith
  have hlogu2 : (2 : ℝ) ≤ Real.log u :=
    (Real.le_log_iff_exp_le hu0).2 hue
  have hlogU : Real.log u ≤ Real.log (U : ℝ) := Real.log_le_log hu0 hceil
  have hlogU1 : 1 < Real.log (U : ℝ) := by linarith
  have hllpos : 0 < Real.log (Real.log (U : ℝ)) := Real.log_pos hlogU1
  have hllmono : Real.log (Real.log u) ≤ Real.log (Real.log (U : ℝ)) :=
    Real.log_le_log (by linarith) hlogU
  have hrounded : FillsAnnulus Z U R D := by
    refine ⟨hu0.trans_le hceil, by exact_mod_cast hR, hD, ?_⟩
    intro v hv hvD
    apply hfill.sample_mem
    · have hbase : u / ((2 * R : ℕ) : ℝ) ≤ (U : ℝ) / R := by
        apply (div_le_div_iff₀ (by positivity) hRpos).2
        push_cast
        nlinarith
      exact hbase.trans hv
    · have htop : (R : ℝ) * U ≤ ((2 * R : ℕ) : ℝ) * u := by
        push_cast
        nlinarith
      exact hvD.trans htop
  refine ⟨U, D, (le_max_left _ _).trans (hu.trans hceil), hlogU1, hrounded, ?_⟩
  apply (div_le_iff₀ hllpos).2
  exact hsmall.trans (mul_le_mul_of_nonneg_left hllmono hη.le)

/-- The epsilon/late-window formulation gives the exact sequential W property;
no real-origin relaxation or omitted asymptotic limit is used. -/
theorem AnnularFilling.windowFilling {Z : LogScale} (hW : AnnularFilling Z) :
    WindowFilling Z := by
  classical
  intro R hR
  have hex (j : ℕ) := hW.integer_witness R hR (1 / ((j : ℝ) + 1))
    (by positivity) ((j : ℝ) + 1)
  choose U D hU hlogU hfill hsmall using hex
  refine ⟨U, D, ?_, hlogU, hfill, ?_⟩
  · apply tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    linarith [hU j]
  · apply squeeze_zero
      (fun j => div_nonneg (by linarith [(hfill j).2.2.1])
        (Real.log_pos (hlogU j)).le)
      hsmall tendsto_one_div_add_atTop_nhds_zero_nat

/-- Exact bridge from the growing consecutive-gap subclass to property W. -/
theorem consecutiveGap_implies_windowFilling {Z : LogScale}
    (hgap : ConsecutiveLogGapLittleO Z) : WindowFilling Z :=
  (consecutiveGap_implies_annularFilling hgap).windowFilling

end ErdosSimilarityGrowingGaps
