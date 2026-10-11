import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker

namespace ErdosSimilarityGrowingGaps

/-! The geometric spacing parameter used by the greedy family may be chosen
independently of the final density parameter.  Taking `σ = 3K` makes the
separation guard `3 ≤ (1/K)σ` automatic and removes the spurious `1/δ`
factor from the candidate quotient. -/
noncomputable def variableRateNodeWitness_of_local_input_bounded
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (c : RoutingTemplate M d) (v : InternalNode M d)
    (U R D σ η : ℝ) (hfill : FillsAnnulus Z U R D)
    (hM : 2 ≤ M) (hσ : 0 < σ) (hD : 0 ≤ D)
    (hη : η * (vertexWindowLength c v : ℝ) ≤
      (vertexWindowLength c v : ℝ) /
        (2 * ((K : ℝ) * (σ + D))))
    (hnode : VariableRateNodeInput (Z := Z) (K := K) (k := k) c v U R D σ)
    (Q : ℕ)
    (hQ : ∀ child, max (((hnode.u child + hnode.ell + (k : ℝ)) /
      (1 / (K : ℝ)) -
      ((hnode.u child + (k : ℝ)) / (K : ℝ) - D)) / σ) 0 + 1 ≤ (Q : ℝ)) :
    Nonempty (VariableRateNodeWitnessBounded (Z := Z) (K := K) (k := k)
      (p := p) c v η hnode.ell Q) := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hs₀ : 0 < (1 / (K : ℝ)) := by positivity
  have hs₁ : 0 < (K : ℝ) := hKpos
  have hell_nonneg : 0 ≤ hnode.ell := by
    have hKD : 0 < (K : ℝ) * (σ + D) := by positivity
    nlinarith [hnode.hell]
  have hη' : η * hnode.ell ≤ hnode.ell /
      (2 * ((K : ℝ) * (σ + D))) := by
    simpa [hnode.ell_eq] using hη
  obtain ⟨B, children, indices, hactive, hinj, hlog, hBQ⟩ :=
    exists_common_greedy_family_bounded (s₀ := 1 / (K : ℝ))
      (s₁ := (K : ℝ)) Z c v k hnode.u hnode.ell D σ η
      (U := U) (R := R) hfill hM hs₀ hs₁ hσ
      hnode.ha hnode.ha_hi hnode.hnum hnode.huk hnode.hwindow hnode.hell
      hnode.hannulus hη' hnode.hsep Q (by
        intro child
        simpa using hQ child)
  exact ⟨{
    B := B
    children := children
    indices := indices
    active_count := hactive
    index_injective := hinj
    logarithmic_gap := hlog
    B_le := hBQ
  }⟩

end ErdosSimilarityGrowingGaps
