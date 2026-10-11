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

/-! The origin anchor becomes the fixed `U/(4K)` tail once the coefficient and
width guards used by the local input bridge hold. -/
theorem eventually_origin_anchor_ge_fixed_tail
    {ι : Type*} {l : Filter ι} (U D : ι → ℝ) (K k : ℝ)
    (hK : 0 < K) (hU : Tendsto U l atTop)
    (hD : ∀ᶠ i in l, D i ≤ U i / (4 * K))
    (hk : ∀ᶠ i in l, |k| ≤ U i / 2) :
    ∀ᶠ i in l, U i / (4 * K) ≤ (U i + k) / K - D i := by
  have hU0 := hU.eventually_ge_atTop (0 : ℝ)
  filter_upwards [hD, hk, hU0] with i hDi hki hUi
  have hkl : -(U i / 2) ≤ k := (abs_le.mp hki).1
  have hku : U i / 2 ≤ U i + k := by linarith
  have hdiv : U i / (2 * K) ≤ (U i + k) / K := by
    have hdiv' : (U i / 2) / K ≤ (U i + k) / K :=
      (div_le_div_iff_of_pos_right hK).2 hku
    convert hdiv' using 1 <;> ring
  have hhalf : U i / (4 * K) + U i / (4 * K) = U i / (2 * K) := by
    field_simp
    ring
  rw [← hhalf] at hdiv
  linarith

/-! Generic width guards for a supplied filled-annulus sequence.  This is the
same conversion used by `windowFilling_sequence_width_asymptotics`, but it
does not choose the sequence from `WindowFilling`; providers can therefore
apply it to their own eventual input. -/
theorem sequence_width_ratio_guards
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (U : ℕ → ℕ) (D : ℕ → ℝ)
    (hUtend : Tendsto (fun j => (U j : ℝ)) atTop atTop)
    (hUlog : ∀ j, 1 < Real.log (U j : ℝ))
    (hUfill : ∀ j, FillsAnnulus Z (U j) (4 * K) (D j))
    (hratio : Tendsto (fun j => D j / Real.log (Real.log (U j : ℝ)))
      atTop (𝓝 0)) :
    D =o[atTop] (fun j => Real.log (Real.log (U j : ℝ))) ∧
    D =o[atTop] (fun j => (U j : ℝ)) ∧
    (∀ᶠ j : ℕ in atTop, 0 ≤ D j) ∧
    (∀ᶠ j : ℕ in atTop, 1 ≤ D j) ∧
    (∀ᶠ j : ℕ in atTop, D j ≤ (U j : ℝ) / (4 * (K : ℝ))) := by
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
    have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) :=
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
    filter_upwards [hDsmall0, hDnonneg, hU_nonneg] with j hj hDj hUj
    rw [Real.norm_eq_abs, abs_of_nonneg hDj,
      Real.norm_eq_abs, abs_of_nonneg hUj] at hj
    calc
      D j ≤ (1 / (4 * (K : ℝ))) * (U j : ℝ) := by simpa using hj
      _ = (U j : ℝ) / (4 * (K : ℝ)) := by ring
  exact ⟨hDlittle, hDlittleU, hDnonneg, hDone, hDsmall⟩

end ErdosSimilarityGrowingGaps
