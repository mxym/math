import ErdosSimilarityGrowingGaps.VariableProviderAssembly

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open Filter Topology Asymptotics

/-! The late provider is fed the actual sequence supplied by `WindowFilling`.
This avoids the invalid quantification over arbitrary early origins and widths:
the provider only has to return certificates eventually along that sequence. -/
structure WindowFillingSequenceVariableProvider (Z : LogScale) : Prop where
  build : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (p α q δ Δ : ℝ),
    0 < p → 0 < α → 0 ≤ q → 0 < δ → δ < 1 → 6 * p < δ →
    0 < Δ → 3 ≤ (1 / (K : ℝ)) * Δ →
    ∀ (Ufun : ℕ → ℕ) (Dfun : ℕ → ℝ),
      Tendsto (fun j => (Ufun j : ℝ)) atTop atTop →
      (∀ j, 1 < Real.log (Ufun j : ℝ)) →
      (∀ j, FillsAnnulus Z (Ufun j) (4 * K) (Dfun j)) →
      Tendsto (fun j => Dfun j / Real.log (Real.log (Ufun j : ℝ))) atTop (𝓝 0) →
      ∀ᶠ j : ℕ in atTop,
        ∃ c : FiniteSequenceRoutingCertificate Z K k p,
          c.template.origin = Ufun j ∧
          c.branching = lateBranching K p δ (Dfun j) ∧
          c.depth = lateDepth K p δ (Dfun j) ∧
          c.template.gap = lateStableGapExplicit K p δ (Dfun j) ∧
          c.rate = lateActivationRate K δ (Dfun j) ∧
          (∀ n ∈ finiteSequenceRoutingTests c, N ≤ n) ∧
          (∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
            n ∈ finiteSequenceRoutingTests c →
            r ∈ sequenceWindowActivations Z n k
              (globalRoutingWindows c.template) →
            q * (input Z n) ^ (r.1.1 + α) <
              routingBufferRadius c.template p)

theorem finiteSequenceBlockerSpec_of_windowFilling_sequence_provider
    {Z : LogScale} (hW : WindowFilling Z)
    (hP : WindowFillingSequenceVariableProvider Z) :
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
  let Δ : ℝ := 3 * (K : ℝ)
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    positivity
  have hΔsep : 3 ≤ (1 / (K : ℝ)) * Δ := by
    dsimp [Δ]
    have hKne : (K : ℝ) ≠ 0 := by
      exact_mod_cast (show K ≠ 0 by omega)
    field_simp [hKne]
    norm_num
  obtain ⟨Ufun, Dfun, hUtend, hUlog, hUfill, hUratio⟩ :=
    hW (4 * K) (by omega)
  have hev := hP.build K hK k N p α q δ Δ hp hα hq hδ hδ₁ hpδ
    hΔ hΔsep Ufun Dfun hUtend hUlog
      (by simpa [Nat.cast_mul] using hUfill) hUratio
  obtain ⟨j, hj⟩ := eventually_atTop.1 hev
  have hj' := hj j (le_refl j)
  obtain ⟨c, horigin, hbranch, hdepth, hgap, hrate, htail, herror⟩ := hj'
  refine ⟨p, hp, hpδ, c, hK, ?_⟩
  intro n hn
  exact ⟨htail n hn, fun r => herror r n⟩

end ErdosSimilarityGrowingGaps
