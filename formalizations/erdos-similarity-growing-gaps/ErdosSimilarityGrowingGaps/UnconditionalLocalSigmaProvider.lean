import ErdosSimilarityGrowingGaps.VariableLocalScheduleAssembly
import ErdosSimilarityGrowingGaps.VariableTemplateSelection
import ErdosSimilarityGrowingGaps.LocalSigmaCertificateAnchor
import ErdosSimilarityGrowingGaps.FinalGuardBridge
import ErdosSimilarityGrowingGaps.SequenceTransferFill
import ErdosSimilarityGrowingGaps.VariableGapBridge
import ErdosSimilarityGrowingGaps.RoutingSpanEnvelope

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The unconditional provider.  All choices are made along the supplied
filled-annulus sequence; the scaled selector reserves a fixed fraction of the
origin for the activation margin. -/
set_option maxHeartbeats 1000000 in
noncomputable def windowFilling_sequence_local_sigma_provider_of_windowFilling
    {Z : LogScale} (hW : WindowFilling Z) :
    WindowFillingSequenceLocalSigmaProvider Z := by
  refine ⟨?_⟩
  intro K hK k N p α q δ σ hp hα hq hδ hδ₁ hpδ hσ hσsep
    U D hUtend hUlog hUfill hratio
  have hp₁ : p ≤ 1 := by nlinarith [hpδ, hδ₁]
  obtain ⟨hDlittle, hDlittleU, hDnonneg, hD₁, hDsmall⟩ :=
    sequence_width_ratio_guards hK U D hUtend hUlog hUfill hratio
  let t : ℝ := min 1 (α / (4 * (K : ℝ)))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht₁ : t ≤ 1 := min_le_left _ _
  have htα : t ≤ α / (4 * (K : ℝ)) := min_le_right _ _
  have hsel := eventually_late_template_length_selection_scaled hK p σ hp hp₁ hσ
    U D hUtend hUlog hUfill hDlittle t ht
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hU4 := hUtend.eventually_ge_atTop (4 : ℝ)
  have hUk := hUtend.eventually_ge_atTop (2 * |(k : ℝ)|)
  have hUlarge := hUtend.eventually_ge_atTop (-2 * (k : ℝ) * ((K : ℝ) + α) / α)
  have hUσ := hUtend.eventually_ge_atTop σ
  obtain ⟨C, hC⟩ := exists_buffer_shift p q hp hq
  have hC' : q * (2 : ℝ) ^ (-C) < p / 32 := by linarith
  have hprefix_bound := exists_integer_bound_on_prefix Z N
  obtain ⟨B, hB⟩ := hprefix_bound
  have hUB := hUtend.eventually_ge_atTop (4 * (K : ℝ) * (B : ℝ))
  have hgaplittle : (fun j => (lateStableGapExplicit K p σ (D j) : ℝ)) =o[atTop]
      (fun j => (U j : ℝ)) := by
    have hDsum : (fun j => σ + D j) =o[atTop]
        (fun j => Real.log (Real.log (U j : ℝ))) := by
      have hc : (fun _ : ℕ => σ) =o[atTop]
          (fun j => Real.log (Real.log (U j : ℝ))) :=
        (isLittleO_const_id_atTop σ).comp_tendsto
          (tendsto_log_log_atTop_of_tendsto _ hUtend)
      convert hc.add hDlittle using 1 <;> ext j <;> ring
    have hDsum₁ : ∀ᶠ j : ℕ in atTop, 1 ≤ σ + D j := by
      filter_upwards [hD₁] with j hj
      linarith
    have hE := variableRoutingEdgeCard_littleO (p / (K : ℝ))
      (by positivity) (by
        apply (div_le_iff₀ hKpos).2
        nlinarith [hp₁]) (fun j => σ + D j) (fun j => (U j : ℝ)) hUtend
      hDsum₁ hDsum
    have hE' : (fun j => (Fintype.card (RoutingEdge
        (lateBranching K p σ (D j)) (lateDepth K p σ (D j))) : ℝ)) =o[atTop]
        (fun j => (U j : ℝ)) := by
      change (fun j : ℕ =>
        ((Fintype.card (RoutingEdge
          (variableBranching (p / (K : ℝ)) (σ + D j))
          (variableDepth (p / (K : ℝ))
            (variableBranching (p / (K : ℝ)) (σ + D j)))) : ℝ))) =o[atTop]
          (fun j => (U j : ℝ))
      exact hE
    exact linearStableGap_littleO_of_edge_littleO p hp _ (fun j => (U j : ℝ))
      hUtend hE'
  have hgap_guard : ∀ᶠ j : ℕ in atTop,
      lateStableGapExplicit K p σ (D j) + 1 ≤ U j := by
    have hg := hgaplittle.bound (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [hg, hUtend.eventually_ge_atTop (4 : ℝ)] with j hj hUj
    have hgj : (lateStableGapExplicit K p σ (D j) : ℝ) ≤ (U j : ℝ) / 4 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hj
      convert hj using 1 <;> ring
    have hgj' : (lateStableGapExplicit K p σ (D j) : ℝ) + 1 ≤ (U j : ℝ) := by
      linarith [hgj, hUj]
    exact_mod_cast hgj'
  have hCbound := hUtend.eventually_ge_atTop (C / (α / (4 * (K : ℝ))))
  filter_upwards [hsel, hDsmall, hDnonneg, hU4, hUk, hUσ, hUB,
    hgap_guard, hCbound, hD₁, hUlarge] with j hj hDj hDnj hU4j hUkj hUσj hUBj hggj hCj hD1j hUlargej
  obtain ⟨L, hP₀, hP₁, hspanBudget⟩ := hj
  let M : ℕ := lateBranching K p σ (D j)
  let d : ℕ := lateDepth K p σ (D j)
  let g : ℕ := lateStableGapExplicit K p σ (D j)
  let tpl : RoutingTemplate M d := { gap := g, baseLength := L, origin := U j }
  have hM : M = lateBranching K p σ (D j) := rfl
  have hd : d = lateDepth K p σ (D j) := rfl
  have hgap : tpl.gap = lateStableGapExplicit K p σ (D j) := rfl
  have hLpos : 0 < L := by
    have hsum : 0 < σ + D j := by linarith [hD1j]
    have harg : 0 < 2 * ((K : ℝ) * (σ + D j)) := by positivity
    have hcceil : 0 < Nat.ceil (2 * ((K : ℝ) * (σ + D j))) := Nat.ceil_pos.mpr harg
    omega
  have horigin : 4 ≤ tpl.origin := by
    dsimp [tpl]
    exact_mod_cast hU4j
  have hcoeff : |(k : ℝ)| ≤ tpl.origin := by
    dsimp [tpl]
    linarith
  have hspanR : (RoutingTemplate.span M tpl.gap tpl.baseLength d : ℝ) ≤ (U j : ℝ) := by
      have hu := lateRoutingSpan_upper_real K p σ (D j) L hp hσ hDnj
      have hbud := hspanBudget
      dsimp [M, d, g, tpl] at hu ⊢
      have htU : t * (U j : ℝ) ≤ (U j : ℝ) := by
        simpa using (mul_le_mul_of_nonneg_right ht₁ (show 0 ≤ (U j : ℝ) by positivity))
      exact hu.trans (hbud.trans htU)
  have hspan : RoutingTemplate.span M tpl.gap tpl.baseLength d ≤ tpl.origin := by
    exact_mod_cast hspanR
  have hDorigin : D j ≤ (tpl.origin : ℝ) := by
    have hden : (1 : ℝ) ≤ 4 * (K : ℝ) := by nlinarith [hKreal]
    have hdiv : (U j : ℝ) / (4 * (K : ℝ)) ≤ (U j : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hden, hU4j]
    dsimp [tpl]
    exact hDj.trans hdiv
  have hbase : 2 * ((K : ℝ) * (σ + D j)) ≤ (tpl.baseLength : ℝ) := by
    have hc : 2 * ((K : ℝ) * (σ + D j)) ≤
        (Nat.ceil (2 * ((K : ℝ) * (σ + D j))) : ℝ) := Nat.le_ceil _
    have hL : (Nat.ceil (2 * ((K : ℝ) * (σ + D j))) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hP₀
    dsimp [tpl]
    exact hc.trans hL
  have hσK : 3 * (K : ℝ) ≤ σ := by
    have hs := hσsep
    field_simp [ne_of_gt hKpos] at hs
    have h := hs
    nlinarith
  have hkhalf : |(k : ℝ)| ≤ (U j : ℝ) / 2 := by nlinarith [hUkj]
  have hinput : ∀ v : InternalNode M d,
      VariableRateNodeInput (Z := Z) (K := K) (k := k) tpl v
        (U j) (4 * (K : ℝ)) (D j) σ := by
    intro v
    apply variableRateNodeInput_of_template_guards tpl v (U j)
      (4 * (K : ℝ)) (D j) σ hK
      (by have hm := lateBranching_ge_two K p σ (D j); rw [hM]; omega) hLpos
      (by simpa [tpl]) (by linarith [hU4j]) (by norm_num) hspanR
      (by show |(k : ℝ)| ≤ (U j : ℝ) / 2; exact hkhalf) hDnj hDj hUσj hbase hσsep
  have hentropy :
      46080 * (M : ℝ) ^ 2 * ((tpl.origin : ℝ) + 1) ^ 2 *
        Real.exp (-(p * lateActivationRate K σ (D j) * ((M : ℝ) - 1) / 2 -
          4 * Real.log 2) * (tpl.baseLength : ℝ)) ≤ p := by
    have hh := variable_entropy_budget_of_length hK p σ (D j) hp hσ hDnj
      (U j) L hP₁
    simpa [M, tpl] using hh.le
  obtain ⟨cert, hcertOrigin, hcertBase, hcertBranch, hcertDepth, hcertGap,
      hcertRate, hanchor⟩ :=
    finiteSequenceRoutingCertificate_of_local_sigma_uniform_budget_with_anchor
      hK hp hp₁ tpl hσ hDnj hM hd hgap horigin hLpos hggj hspan hcoeff
      hentropy (U j) (4 * (K : ℝ)) (by simpa [tpl] using hUfill j) rfl hinput hDorigin hσK
  have hcertOriginNat : cert.template.origin = U j := by
    exact_mod_cast hcertOrigin
  refine ⟨cert, hcertOriginNat, hcertBranch, hcertDepth, hcertGap, hcertRate, ?_, ?_⟩
  · have hA : (U j : ℝ) / (4 * (K : ℝ)) ≤
        ((U j : ℝ) + (k : ℝ)) / (K : ℝ) - D j := by
      have hklo : -(U j : ℝ) / 2 ≤ (k : ℝ) := by
        have hkl := (abs_le.mp hkhalf).1
        nlinarith [hkl]
      have hku : (U j : ℝ) / 2 ≤ (U j : ℝ) + (k : ℝ) := by linarith
      have hdv : (U j : ℝ) / (2 * (K : ℝ)) ≤
          ((U j : ℝ) + (k : ℝ)) / (K : ℝ) := by
        have hh : ((U j : ℝ) / 2) / (K : ℝ) ≤
            ((U j : ℝ) + (k : ℝ)) / (K : ℝ) :=
          (div_le_div_iff_of_pos_right hKpos).2 hku
        convert hh using 1 <;> ring
      have heq : (U j : ℝ) / (4 * (K : ℝ)) + (U j : ℝ) / (4 * (K : ℝ)) =
          (U j : ℝ) / (2 * (K : ℝ)) := by field_simp; ring
      rw [← heq] at hdv
      linarith [hDj]
    have hlow : ∀ v i, (U j : ℝ) / (4 * (K : ℝ)) ≤ Z.z (cert.indices v i) := by
      intro v i
      exact hA.trans (by simpa [hcertOrigin] using hanchor v i)
    exact finiteSequenceRoutingTests_tail_of_log_lower cert N
      ((U j : ℝ) / (4 * (K : ℝ)))
      (by
        intro m hm
        have hm' := hB m hm
        have hBreal : (B : ℝ) ≤ (U j : ℝ) / (4 * (K : ℝ)) := by
          apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (K : ℝ))).2
          calc
            (B : ℝ) * (4 * (K : ℝ)) = 4 * (K : ℝ) * (B : ℝ) := by ring
            _ ≤ (U j : ℝ) := hUBj
        exact hm'.trans_le hBreal) hlow
  · intro r n hn hr
    have hO : 1 ≤ cert.template.origin := by omega
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hr
    have hrpos : 0 < r.1.1 := by
      exact lt_of_lt_of_le (by positivity) r.1.2.1
    have hzpos : 0 < Z.z n := Z.positive n
    have hprod : r.1.1 * Z.z n ≤ (K : ℝ) * Z.z n :=
      mul_le_mul_of_nonneg_right r.1.2.2 hzpos.le
    have hz : (((cert.template.origin : ℝ) + (k : ℝ)) / (K : ℝ)) ≤ Z.z n := by
      apply (div_le_iff₀ hKpos).2
      have hstart := globalRoutingWindow_start_ge_origin cert.template e
      linarith [he.1, hprod]
    apply herror_of_global_window_margin_shift (k := k) cert.template r n hO hα hq hp hC'
    · intro e'
      have hst := globalRoutingWindow_start_ge_origin cert.template e'
      have hαz := mul_le_mul_of_nonneg_left hz hα.le
      have hCsmall : C ≤ (α / (4 * (K : ℝ))) * (U j : ℝ) := by
        have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < α / (4 * (K : ℝ)))).1 hCj
        simpa [mul_comm] using hh
      have hspanC : (RoutingTemplate.span cert.branching cert.template.gap cert.template.baseLength cert.depth : ℝ) + C ≤
          (α / (2 * (K : ℝ))) * (U j : ℝ) := by
        have hspan' : (RoutingTemplate.span cert.branching cert.template.gap cert.template.baseLength cert.depth : ℝ) ≤
            t * (U j : ℝ) := by
          have hupper := lateRoutingSpan_upper_real K p σ (D j) L hp hσ hDnj
          have hlate := hupper.trans hspanBudget
          simpa [lateRoutingSpan, hcertBranch, hcertDepth, hcertGap,
            hcertBase, hcertOriginNat, M, d, g, tpl] using hlate
        have ht' : t * (U j : ℝ) ≤ (α / (4 * (K : ℝ))) * (U j : ℝ) :=
          mul_le_mul_of_nonneg_right htα (by positivity)
        calc
          _ ≤ t * (U j : ℝ) + C := by
            simpa [add_comm] using (add_le_add_right hspan' C)
          _ ≤ (α / (4 * (K : ℝ))) * (U j : ℝ) + (α / (4 * (K : ℝ))) * (U j : ℝ) := by
            gcongr
          _ = _ := by ring
      have hrewrite : (α / (2 * (K : ℝ))) * (U j : ℝ) ≤
          (k : ℝ) + α * (((U j : ℝ) + (k : ℝ)) / (K : ℝ)) := by
        field_simp [ne_of_gt hKpos]
        have hlarge : 0 ≤ α * (U j : ℝ) + 2 * (k : ℝ) * ((K : ℝ) + α) := by
          have hlarge' := (div_le_iff₀ hα).1 hUlargej
          nlinarith
        nlinarith
      have hst' : (U j : ℝ) ≤ (globalRoutingWindows cert.template e').1 := by
        simpa [hcertOrigin] using hst
      have hαz' : α * (((U j : ℝ) + (k : ℝ)) / (K : ℝ)) ≤
          α * Z.z n := by
        simpa [hcertOrigin] using hαz
      calc
        (cert.template.origin : ℝ) +
              (RoutingTemplate.span cert.branching cert.template.gap
                cert.template.baseLength cert.depth : ℝ) + C =
            (U j : ℝ) +
              (RoutingTemplate.span cert.branching cert.template.gap
                cert.template.baseLength cert.depth : ℝ) + C := by
                  rw [hcertOrigin]
        _ ≤ (U j : ℝ) +
              (α / (2 * (K : ℝ))) * (U j : ℝ) := by
                linarith [hspanC]
        _ ≤ (U j : ℝ) + (k : ℝ) +
              α * (((U j : ℝ) + (k : ℝ)) / (K : ℝ)) := by
                linarith [hrewrite]
        _ = (cert.template.origin : ℝ) + (k : ℝ) +
              α * (((cert.template.origin : ℝ) + (k : ℝ)) / (K : ℝ)) := by
                rw [hcertOrigin]
        _ ≤ (globalRoutingWindows cert.template e').1 + (k : ℝ) + α * Z.z n := by
                linarith [hst', hαz']
    · exact hr

end ErdosSimilarityGrowingGaps
