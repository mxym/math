import ErdosSimilarityGrowingGaps.VariableBridge
import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The edge-cardinality and explicit stable-gap terms are sublinear in a
late origin whenever the variable width is `o(log log U)`.  These lemmas are
kept separate from the finite certificate: they discharge the numerical
envelopes needed by the span theorem without choosing any routing lists. -/

theorem variableRoutingEdgeCard_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (Fintype.card (RoutingEdge
      (variableBranching p (D i))
      (variableDepth p (variableBranching p (D i)))) : ℝ)) =o[l] U := by
  let M : ι → ℕ := fun i => variableBranching p (D i)
  let d : ι → ℕ := fun i => variableDepth p (M i)
  have hcoef := variable_edge_coefficient_littleO p hp hp₁ D U hU hD₁ hD
  have hbig : (fun i =>
      (Fintype.card (RoutingEdge (M i) (d i)) : ℝ)) =O[l]
      (fun i => ((((4 * M i) ^ (d i + 1) : ℕ) : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with i
    have hM : 2 ≤ M i := by
      dsimp [M]
      exact variableBranching_ge_two _ _
    have hcard := routingEdge_card_le_pow (M i) (d i) hM
    have hpow : (2 * M i) ^ (d i + 1) ≤ (4 * M i) ^ (d i + 1) := by
      apply Nat.pow_le_pow_left
      omega
    have hcard' : Fintype.card (RoutingEdge (M i) (d i)) ≤
        (4 * M i) ^ (d i + 1) := hcard.trans hpow
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    simpa only [one_mul] using (show
      (Fintype.card (RoutingEdge (M i) (d i)) : ℝ) ≤
        (((4 * M i) ^ (d i + 1) : ℕ) : ℝ) by exact_mod_cast hcard')
  have hcoef' := hcoef
  exact hbig.trans_isLittleO hcoef'

theorem variableStableGapExplicit_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => ((linearStableGap
      (Fintype.card (RoutingEdge
        (variableBranching p (D i))
        (variableDepth p (variableBranching p (D i))))) p : ℕ) : ℝ)) =o[l] U := by
  let E : ι → ℝ := fun i =>
    (Fintype.card (RoutingEdge
      (variableBranching p (D i))
      (variableDepth p (variableBranching p (D i)))) : ℝ)
  let G : ι → ℝ := fun i =>
    ((linearStableGap
      (Fintype.card (RoutingEdge
        (variableBranching p (D i))
        (variableDepth p (variableBranching p (D i)))) ) p : ℕ) : ℝ)
  have hE : E =o[l] U := by
    exact variableRoutingEdgeCard_littleO p hp hp₁ D U hU hD₁ hD
  have hconst : (fun _ : ι => (1 : ℝ)) =o[l] U := by
    apply isLittleO_const_left.2
    right
    exact tendsto_norm_atTop_atTop.comp hU
  have hlin : (fun i => 8 / p * E i + 1) =o[l] U := by
    have hscale := hE.const_mul_left (8 / p)
    have hadd := hscale.add hconst
    simpa [Function.comp_def] using hadd
  have hU₀ : ∀ᶠ i in l, 0 ≤ U i :=
    hU.eventually (eventually_ge_atTop (0 : ℝ))
  have hGnonneg : ∀ᶠ i in l, 0 ≤ G i := by
    filter_upwards [] with i
    dsimp [G]
    positivity
  have hbound : ∀ᶠ i in l, G i ≤ 8 / p * E i + 1 := by
    filter_upwards [] with i
    dsimp [G, E]
    have hupper := linearStableGap_upper
      (Fintype.card (RoutingEdge
        (variableBranching p (D i))
        (variableDepth p (variableBranching p (D i)))) ) p hp
    calc
      ((linearStableGap
        (Fintype.card (RoutingEdge
          (variableBranching p (D i))
          (variableDepth p (variableBranching p (D i)))) ) p : ℕ) : ℝ) ≤
          8 * (Fintype.card (RoutingEdge
            (variableBranching p (D i))
            (variableDepth p (variableBranching p (D i)))) : ℝ) / p + 1 := hupper
      _ = 8 / p * (Fintype.card (RoutingEdge
          (variableBranching p (D i))
          (variableDepth p (variableBranching p (D i)))) : ℝ) + 1 := by ring
  exact littleO_of_eventually_nonneg_le hlin hU₀ hGnonneg hbound

end ErdosSimilarityGrowingGaps
