import ErdosSimilarityGrowingGaps.VariableSigmaCertificate

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The uniform local-sigma constructor keeps the greedy witness internally.
This companion returns the resulting certificate together with the origin
anchor carried by every retained logarithmic sample.  The original constructor
is intentionally left unchanged for callers that only need the certificate. -/
theorem finiteSequenceRoutingCertificate_of_local_sigma_uniform_budget_with_anchor
    {Z : LogScale} {K : ℕ} {k : ℤ} {p σ D : ℝ} {M d : ℕ}
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (tpl : RoutingTemplate M d)
    (hσ : 0 < σ) (hD : 0 ≤ D)
    (hM : M = lateBranching K p σ D)
    (hd : d = lateDepth K p σ D)
    (hgap : tpl.gap = lateStableGapExplicit K p σ D)
    (horigin : 4 ≤ tpl.origin) (hlength : 0 < tpl.baseLength)
    (hgap_guard : tpl.gap + 1 ≤ tpl.origin)
    (hspan : RoutingTemplate.span M tpl.gap tpl.baseLength d ≤ tpl.origin)
    (hcoeff : |(k : ℝ)| ≤ tpl.origin)
    (hentropy :
      46080 * (M : ℝ) ^ 2 * ((tpl.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * lateActivationRate K σ D * ((M : ℝ) - 1) / 2 -
          4 * Real.log 2) * (tpl.baseLength : ℝ)) ≤ p)
    (U R : ℝ) (hfill : FillsAnnulus Z U R D)
    (horigin_real : (tpl.origin : ℝ) = U)
    (hinput : ∀ v : InternalNode M d,
      VariableRateNodeInput (Z := Z) (K := K) (k := k) tpl v U R D σ)
    (hDorigin : D ≤ (tpl.origin : ℝ))
    (hσK : 3 * (K : ℝ) ≤ σ) :
    ∃ c : FiniteSequenceRoutingCertificate Z K k p,
      (∀ v : InternalNode c.branching c.depth, ∀ i,
        ((c.template.origin : ℝ) + (k : ℝ)) / (K : ℝ) - D ≤
          Z.z (c.indices v i)) := by
  let T : ℝ := (tpl.origin : ℝ) +
    (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) + |(k : ℝ)| + 2
  have hupper : ∀ v : InternalNode M d, ∀ child,
      (hinput v).u child + (hinput v).ell + (k : ℝ) ≤ T := by
    intro v child
    have hspanR : (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) ≤ U := by
      have hspanR0 : (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) ≤
          (tpl.origin : ℝ) := by exact_mod_cast hspan
      simpa [horigin_real] using hspanR0
    have hh := canonical_selector_window_upper_exact tpl v
      (by rw [hM]; have hh := lateBranching_ge_two K p σ D; omega)
      hlength U k horigin_real hspanR
    dsimp [T]
    have hchild := hh child
    have hwin := (hinput v).hwindow child
    have hleft :
        (hinput v).u child + (hinput v).ell + (k : ℝ) =
          (tpl.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
            (vertexWindowLength tpl v : ℝ) + (k : ℝ) := by
      rw [← hwin.1, (hinput v).ell_eq]
    calc
      (hinput v).u child + (hinput v).ell + (k : ℝ) =
          (tpl.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
            (vertexWindowLength tpl v : ℝ) + (k : ℝ) := hleft
      _ ≤ U + (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) + |(k : ℝ)| :=
        hchild
      _ ≤ (tpl.origin : ℝ) + (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) +
          |(k : ℝ)| + 2 := by rw [horigin_real]; linarith
  have hQcandidate : (((M - 1) *
      (variableNodeUniformBudget K T D σ + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * ((tpl.origin : ℝ) +
        (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) + |(k : ℝ)| + 2) := by
    dsimp [T]
    exact variable_uniform_candidate_count_of_template hK tpl σ D hσK hD
      horigin (by exact_mod_cast hspan) hcoeff hDorigin
  have hQ : ∀ v : InternalNode M d, ∀ child,
      max ((((hinput v).u child + (hinput v).ell + (k : ℝ)) /
        (1 / (K : ℝ)) -
        (((hinput v).u child + (k : ℝ)) / (K : ℝ) - D)) / σ) 0 + 1 ≤
          (variableNodeUniformBudget K T D σ : ℝ) := by
    intro v child
    exact variableNodeUniformBudget_child_bound
      (by exact_mod_cast (show 0 < K by omega))
      (fun child => (hinput v).u child) (hinput v).ell D σ T k hσ
      (fun child => (hinput v).huk child)
      (fun child => hupper v child) child
  let witness := variableRateBoundedWitness_of_inputs (p := p) hK tpl U R D σ hfill
    (by rw [hM]; exact lateBranching_ge_two K p σ D) hσ hD hinput
    (variableNodeUniformBudget K T D σ) hQ
  let cert := finiteSequenceRoutingCertificate_of_variable_rate_bounded_data
    hK hp hp₁ tpl σ D hσ hD hM hd hgap horigin hlength hgap_guard hspan hcoeff
    hentropy (variableNodeUniformBudget K T D σ) witness hQcandidate
  refine ⟨cert, ?_⟩
  intro v i
  change ((tpl.origin : ℝ) + (k : ℝ)) / (K : ℝ) - D ≤
      Z.z ((witness v).indices i)
  have hlow := (witness v).index_lower i
  have hstart_nat := tpl.edgeStart_ge_origin
    (RoutingTemplate.selectorRoutingEdge ⟨v, (witness v).children i⟩)
  have hstart : (tpl.origin : ℝ) ≤
      (tpl.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, (witness v).children i⟩) : ℝ) := by
    exact_mod_cast hstart_nat
  have hdiv : ((tpl.origin : ℝ) + (k : ℝ)) / (K : ℝ) ≤
      ((tpl.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, (witness v).children i⟩) : ℝ) + (k : ℝ)) / (K : ℝ) := by
    apply (div_le_div_iff_of_pos_right (by exact_mod_cast
      (show 0 < K by omega))).2
    linarith
  have hanchor : ((tpl.origin : ℝ) + (k : ℝ)) / (K : ℝ) - D ≤
      Z.z ((witness v).indices i) := (sub_le_sub_right hdiv D).trans hlow
  exact hanchor

end ErdosSimilarityGrowingGaps
