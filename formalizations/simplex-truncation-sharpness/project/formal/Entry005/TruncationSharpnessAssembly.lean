import Entry005.TruncationMaximum
import Entry005.TruncationCentroid
import Entry005.TruncationPower

noncomputable section
open MeasureTheory

namespace Entry005

/-- A transparent assembly boundary: the actual geometric defect equality is
the only supplied premise. Compact body, nonempty interior, the genuine global
maximum simplex and excess about its own centroid are proved dependencies.
This implication alone is not a proof of the geometric identity or sharpness. -/
theorem truncation_sharpness_from_actual_defect_formula
    (hformula : ∀ d : ℕ, 3 ≤ d → ∀ t : ℝ, 0 < t → t < 1 →
      entryDefect (truncationSet d t) = truncationRationalDefect d t) :
    truncationSharpnessGoal := by
  intro d hd α hα C ε _hC hε
  obtain ⟨t, ht, htε, hp, hs, hb⟩ :=
    truncation_conditional_scalar_power_obstruction hd
      (fun t => entryDefect (truncationSet d t)) (hformula d hd) hα C hε
  have ht1 : t < 1 := htε.trans_le (min_le_right ε 1)
  have hdpos : 0 < d := by omega
  let i : Fin d := ⟨0, hdpos⟩
  let K := truncationBody d t hdpos ht ht1
  let S := truncationSimplex t i (by linarith : t ≠ 1)
  refine ⟨t, ht, htε, K, rfl, truncationSet_interior_nonempty hdpos ht ht1,
    S, truncationSimplex_maximumInscribed hdpos t ht ht1 i, hp, hs, ?_⟩
  change C * entryDefect (truncationSet d t) ^ α < excess (truncationSet d t) S
  rw [truncation_simplex_excess_exact (by omega) t ht.le ht1 i S rfl]
  exact hb

/-- In particular the obstructing maximum uses the actual original centroid. -/
theorem truncation_chosen_maximum_and_excess {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (i : Fin d) :
    maximumInscribed (truncationBody d t (by omega) ht0 ht1)
      (truncationSimplex t i (by linarith)) ∧
    excess (truncationSet d t) (truncationSimplex t i (by linarith)) = (d + 1 : ℝ) * t := by
  exact ⟨truncationSimplex_maximumInscribed (by omega) t ht0 ht1 i,
    truncation_simplex_excess_exact hd t ht0.le ht1 i _ rfl⟩

end Entry005
