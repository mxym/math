import ErdosSimilarityGrowingGaps.AnnulusSequence
import ErdosSimilarityGrowingGaps.RoutingSchedule

namespace ErdosSimilarityGrowingGaps

open Filter Topology

/-!  A sequential version of the preceding-origin scheduling lemma.  It is
the exact point at which the abstract late annulus is synchronized with the
finite routing template. -/
theorem WindowFilling.exists_scheduled_annulus
    {Z : LogScale} (hW : WindowFilling Z)
    (K : ℕ) (hK : 2 ≤ K) (k : ℤ) (N : ℕ) (p : ℝ) (hp : 0 < p)
    (R : ℕ) (hR : 2 ≤ R) (η : ℝ) (hη : 0 < η) :
    ∃ U : ℕ → ℕ, ∃ D : ℕ → ℝ, ∃ j : ℕ, ∃ s : RoutingSchedule K k N p,
      s.template.origin = U j ∧
      1 < Real.log (U j : ℝ) ∧
      FillsAnnulus Z (U j) R (D j) ∧
      D j / Real.log (Real.log (U j : ℝ)) < η := by
  obtain ⟨U, D, hUtend, hUlog, hUfill, hUratio⟩ := hW R hR
  have hSched := routing_schedule_eventually_at_origin K hK k N p hp
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 hSched
  have hlate : ∀ᶠ j : ℕ in atTop, U₀ ≤ U j := by
    have hreal : ∀ᶠ j : ℕ in atTop, (U₀ : ℝ) ≤ (U j : ℝ) :=
      hUtend.eventually (eventually_ge_atTop (U₀ : ℝ))
    filter_upwards [hreal] with j hj
    exact_mod_cast hj
  have hsched : ∀ᶠ j : ℕ in atTop, ∃ s : RoutingSchedule K k N p,
      s.template.origin = U j := by
    filter_upwards [hlate] with j hj
    obtain ⟨s, hs⟩ := hU₀ (U j) hj
    exact ⟨s, hs⟩
  have hratio : ∀ᶠ j : ℕ in atTop,
      D j / Real.log (Real.log (U j : ℝ)) < η :=
    hUratio.eventually (Iio_mem_nhds hη)
  obtain ⟨j, hjS, hjr⟩ := (hsched.and hratio).exists
  obtain ⟨s, hs⟩ := hjS
  exact ⟨U, D, j, s, hs, hUlog j, hUfill j, hjr⟩

end ErdosSimilarityGrowingGaps
