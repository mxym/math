import Entry005.TruncationDefinitions
import Entry005.TruncationSimplexVolume
import Entry005.FiniteHalfspaceFacets

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def truncationAmbientSimplex (d : ℕ) (r : ℝ) : Set (Space d) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

theorem truncation_ambient_simplex_measurable (d : ℕ) (r : ℝ) :
    MeasurableSet (truncationAmbientSimplex d r) := by
  unfold truncationAmbientSimplex
  measurability

theorem truncation_ambient_simplex_volume (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (truncationAmbientSimplex d r) =
      ENNReal.ofReal (r ^ d / (d.factorial : ℝ)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    (truncation_ambient_simplex_measurable d r).nullMeasurableSet]
  exact OAI.ProjectionCounterexample.volume_coordinateSimplex d r hr

theorem truncation_ambient_simplex_real_volume (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (volume (truncationAmbientSimplex d r)).toReal = r ^ d / (d.factorial : ℝ) := by
  rw [truncation_ambient_simplex_volume d r hr, ENNReal.toReal_ofReal]
  positivity

theorem truncation_sum_level_volume_zero {d : ℕ} (hd : 0 < d) (r : ℝ) :
    volume {x : Space d | ∑ i, x i = r} = 0 := by
  let u : Space d := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hu : u ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Space d => x ⟨0, hd⟩) h
    norm_num [u] at hc
  have hi (x : Space d) : inner ℝ u x = ∑ i, x i := by
    simp [PiLp.inner_apply, u, RCLike.inner_apply]
  simpa only [hi] using inner_level_volume_zero u hu r

theorem truncation_union_removed_simplex {d : ℕ} {t : ℝ} (ht : t ≤ 1) :
    truncationSet d t ∪ truncationAmbientSimplex d t = truncationAmbientSimplex d 1 := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.2⟩
    · exact ⟨hx.1, hx.2.trans ht⟩
  · intro hx
    by_cases hs : t ≤ ∑ i, x i
    · exact Or.inl ⟨hx.1, hs, hx.2⟩
    · exact Or.inr ⟨hx.1, le_of_not_ge hs⟩

theorem truncation_removed_overlap_volume_zero {d : ℕ} (hd : 0 < d) (t : ℝ) :
    volume (truncationSet d t ∩ truncationAmbientSimplex d t) = 0 := by
  apply measure_mono_null _ (truncation_sum_level_volume_zero hd t)
  intro x hx
  exact le_antisymm hx.2.2 hx.1.2.1

/-- Exact ordinary volume of the actual coordinate truncation, with only the
actual truncation parameter and positive ambient dimension as assumptions. -/
theorem truncation_actual_volume {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume (truncationSet d t)).toReal = (1 - t ^ d) / (d.factorial : ℝ) := by
  have hsum := measure_union_add_inter (μ := (volume : Measure (Space d)))
    (truncationSet d t) (truncation_ambient_simplex_measurable d t)
  rw [truncation_union_removed_simplex ht1,
    truncation_removed_overlap_volume_zero hd t, add_zero] at hsum
  have hbig : volume (truncationAmbientSimplex d 1) ≠ ⊤ := by
    rw [truncation_ambient_simplex_volume d 1 zero_le_one]
    exact ENNReal.ofReal_ne_top
  have hsmall : volume (truncationAmbientSimplex d t) ≠ ⊤ := by
    rw [truncation_ambient_simplex_volume d t ht0]
    exact ENNReal.ofReal_ne_top
  have hK : volume (truncationSet d t) ≠ ⊤ :=
    ne_top_of_le_ne_top hbig (measure_mono (fun _ hx => ⟨hx.1, hx.2.2⟩))
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hK hsmall,
    truncation_ambient_simplex_real_volume d 1 zero_le_one,
    truncation_ambient_simplex_real_volume d t ht0, one_pow] at hreal
  rw [sub_div]
  linarith

end Entry005
