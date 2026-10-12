import ErdosSimilarityGrowingGaps.AsymptoticProducts
import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-- The sequential form of `WindowFilling` supplies exactly the asymptotic
width estimates needed by a variable routing schedule.  In particular, the
ratio limit is converted to a genuine `IsLittleO` statement using the strict
positivity of the iterated logarithm. -/
theorem windowFilling_sequence_width_asymptotics
    {Z : LogScale} (hW : WindowFilling Z) (R : ℕ) (hR : 2 ≤ R)
    {K : ℕ} (hK : 2 ≤ K) :
    ∃ (U : ℕ → ℕ) (D : ℕ → ℝ),
      Tendsto (fun j => (U j : ℝ)) atTop atTop ∧
      (∀ j, 1 < Real.log (U j : ℝ)) ∧
      (∀ j, FillsAnnulus Z (U j) R (D j)) ∧
      D =o[atTop] (fun j => Real.log (Real.log (U j : ℝ))) ∧
      D =o[atTop] (fun j => (U j : ℝ)) ∧
      (∀ᶠ j : ℕ in atTop, 0 ≤ D j) ∧
      (∀ᶠ j : ℕ in atTop, 1 ≤ D j) ∧
      (∀ᶠ j : ℕ in atTop, D j ≤ (U j : ℝ) / (4 * (K : ℝ))) := by
  obtain ⟨U, D, hUtend, hUlog, hUfill, hratio⟩ := hW R hR
  have hDlittle : D =o[atTop]
      (fun j => Real.log (Real.log (U j : ℝ))) := by
    refine (isLittleO_iff_tendsto (fun j hz => ?_)).2 ?_
    · have hpos : 0 < Real.log (Real.log (U j : ℝ)) :=
        Real.log_pos (hUlog j)
      exfalso
      linarith
    · simpa only [Function.comp_apply] using hratio
  have hLLlittle : (fun j => Real.log (Real.log (U j : ℝ))) =o[atTop]
      (fun j => (U j : ℝ)) := by
    have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x) :=
      Real.isLittleO_log_id_atTop
    have h2 : (fun j => Real.log (Real.log (U j : ℝ))) =o[atTop]
        (fun j => Real.log (U j : ℝ)) := by
      simpa [Function.comp_def] using
        h1.comp_tendsto (Real.tendsto_log_atTop.comp hUtend)
    have h3 : (fun j => Real.log (U j : ℝ)) =o[atTop]
        (fun j => (U j : ℝ)) := by
      simpa [Function.comp_def] using h1.comp_tendsto hUtend
    exact h2.trans h3
  have hDlittleU : D =o[atTop] (fun j => (U j : ℝ)) :=
    hDlittle.trans hLLlittle
  have hDnonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ D j := by
    filter_upwards [] with j
    linarith [(hUfill j).2.2.1]
  have hDone : ∀ᶠ j : ℕ in atTop, 1 ≤ D j := by
    filter_upwards [] with j
    exact (hUfill j).2.2.1
  have hU_nonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ (U j : ℝ) :=
    hUtend.eventually (eventually_ge_atTop (0 : ℝ))
  have hDsmall0 := hDlittleU.bound (by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    positivity : (0 : ℝ) < 1 / (4 * (K : ℝ)))
  have hDsmall : ∀ᶠ j : ℕ in atTop,
      D j ≤ (U j : ℝ) / (4 * (K : ℝ)) := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    filter_upwards [hDsmall0, hDnonneg, hU_nonneg] with j hj hDj hUj
    rw [Real.norm_eq_abs, abs_of_nonneg hDj,
      Real.norm_eq_abs, abs_of_nonneg hUj] at hj
    calc
      D j ≤ (1 / (4 * (K : ℝ))) * (U j : ℝ) := by simpa using hj
      _ = (U j : ℝ) / (4 * (K : ℝ)) := by ring
  exact ⟨U, D, hUtend, hUlog, hUfill, hDlittle, hDlittleU,
    hDnonneg, hDone, hDsmall⟩

end ErdosSimilarityGrowingGaps
