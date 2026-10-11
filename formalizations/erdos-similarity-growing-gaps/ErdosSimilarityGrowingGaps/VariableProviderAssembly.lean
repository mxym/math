import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker
import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open Filter Topology Asymptotics
open scoped BigOperators

/-! A direct variable-schedule provider.  Unlike the legacy provider, this
interface does not quantify over a preselected `RoutingSchedule`: the
branching, depth, gap, and base length may all depend on the supplied filled
annulus.  Its fields expose the scalar choices, so an implementation cannot
silently fall back to a fixed-rate tree. -/
structure WindowFillingVariableSequenceProvider (Z : LogScale) : Prop where
  build : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (p α q δ Δ : ℝ),
    0 < p → 0 < α → 0 ≤ q → 0 < δ → δ < 1 → 6 * p < δ →
    0 < Δ → 3 ≤ (1 / (K : ℝ)) * Δ →
    ∀ (U : ℕ) (R D : ℝ),
      FillsAnnulus Z (U : ℝ) R D →
      ∃ c : FiniteSequenceRoutingCertificate Z K k p,
        c.template.origin = U ∧
        c.branching = lateBranching K p δ D ∧
        c.depth = lateDepth K p δ D ∧
        c.template.gap = lateStableGapExplicit K p δ D ∧
        c.rate = lateActivationRate K δ D ∧
        (∀ n ∈ finiteSequenceRoutingTests c, N ≤ n) ∧
        (∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
          n ∈ finiteSequenceRoutingTests c →
          r ∈ sequenceWindowActivations Z n k
            (globalRoutingWindows c.template) →
          q * (input Z n) ^ (r.1.1 + α) <
            routingBufferRadius c.template p)

/-! The assembly theorem is fully kernel-checked.  The only pending work is
the construction of the direct provider above; once supplied, the theorem
selects `p = δ/12`, obtains a late annulus from `WindowFilling`, and feeds its
variable certificate to the already proved finite blocker. -/
theorem finiteSequenceBlockerSpec_of_windowFilling_variable_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingVariableSequenceProvider Z) :
    FiniteSequenceBlockerSpec Z := by
  refine ⟨?_⟩
  intro K hK k N α q δ hα hq hδ hδ₁
  let p : ℝ := δ / 12
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hpδ : 6 * p < δ := by
    dsimp [p]
    nlinarith
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  let Δ : ℝ := 3 * (K : ℝ)
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hΔsep : 3 ≤ (1 / (K : ℝ)) * Δ := by
    dsimp [Δ]
    have hK0 : (K : ℝ) ≠ 0 := ne_of_gt hKpos
    rw [one_div]
    field_simp [hK0]
    exact le_rfl
  obtain ⟨U, D, hUN, hlog, hfill, _hratio⟩ :=
    WindowFilling.exists_late_annulus hW (4 * K) (by omega)
      (max (N : ℝ) 1) (K : ℝ) (by positivity) hKpos
  have hD : 0 ≤ D := by
    linarith [hfill.2.2.1]
  have hfill' : FillsAnnulus Z (U : ℝ) (4 * (K : ℝ)) D := by
    simpa using hfill
  obtain ⟨c, horigin, hbranch, hdepth, hgap, hrate, htail, herror⟩ :=
    hP.build K hK k N p α q δ Δ hp hα hq hδ hδ₁ hpδ hΔ hΔsep
      U (4 * (K : ℝ)) D hfill'
  refine ⟨p, hp, hpδ, c, hK, ?_⟩
  intro n hn
  exact ⟨htail n hn, fun r => herror r n⟩

end ErdosSimilarityGrowingGaps
