import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The `o(log log U)` width condition also supplies the elementary linear
guard needed by the variable routing input.  This is kept separate from the
construction: it only repackages the sequential witness already present in
`WindowFilling`. -/
theorem WindowFilling.eventually_width_le_linear
    {Z : LogScale} (hW : WindowFilling Z) (R : ℕ) (hR : 2 ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (U : ℕ → ℕ) (D : ℕ → ℝ),
      Tendsto (fun j => (U j : ℝ)) atTop atTop ∧
      (∀ j, 1 < Real.log (U j : ℝ)) ∧
      (∀ j, FillsAnnulus Z (U j) R (D j)) ∧
      (∀ᶠ j : ℕ in atTop, D j ≤ ε * (U j : ℝ)) := by
  obtain ⟨U, D, hU, hlog, hfill, hratio⟩ := hW R hR
  have hlogU : Tendsto (fun j => Real.log (U j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hU
  have hLLlog : (fun j => Real.log (Real.log (U j : ℝ))) =o[atTop]
      (fun j => Real.log (U j : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto hlogU
  have hlogUo : (fun j => Real.log (U j : ℝ)) =o[atTop]
      (fun j => (U j : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto hU
  have hLLo : (fun j => Real.log (Real.log (U j : ℝ))) =o[atTop]
      (fun j => (U j : ℝ)) := hLLlog.trans hlogUo
  have hLLbound := hLLo.bound hε
  have hratio1 : ∀ᶠ j : ℕ in atTop,
      D j / Real.log (Real.log (U j : ℝ)) ≤ 1 := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with j hj
    exact hj.le
  have hU₀ : ∀ᶠ j : ℕ in atTop, 0 ≤ (U j : ℝ) := by
    filter_upwards [hU.eventually (eventually_ge_atTop (0 : ℝ))] with j hj
    exact hj
  have hLL₀ : ∀ᶠ j : ℕ in atTop,
      0 ≤ Real.log (Real.log (U j : ℝ)) := by
    filter_upwards [] with j
    exact (Real.log_pos (hlog j)).le
  have hDleLL : ∀ᶠ j : ℕ in atTop,
      D j ≤ Real.log (Real.log (U j : ℝ)) := by
    filter_upwards [hratio1, hLL₀] with j hj hLLj
    have hdiv := (div_le_iff₀ (Real.log_pos (hlog j))).1 hj
    simpa using hdiv
  have hLLle : ∀ᶠ j : ℕ in atTop,
      Real.log (Real.log (U j : ℝ)) ≤ ε * (U j : ℝ) := by
    filter_upwards [hLLbound, hU₀, hLL₀] with j hj hUj hLLj
    rw [Real.norm_eq_abs, abs_of_nonneg hLLj,
      Real.norm_eq_abs, abs_of_nonneg hUj] at hj
    exact hj
  refine ⟨U, D, hU, hlog, hfill, ?_⟩
  filter_upwards [hDleLL, hLLle] with j hj hLj
  exact hj.trans hLj

end ErdosSimilarityGrowingGaps
