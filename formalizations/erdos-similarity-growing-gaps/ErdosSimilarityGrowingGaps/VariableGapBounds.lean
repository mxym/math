import ErdosSimilarityGrowingGaps.VariableBridge

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Concrete edge and stable-gap envelopes for the variable late schedule.  The
edge-cardinality estimate is deliberately separated from the routing witness:
it only uses the finite tree cardinality bound and the logarithmic width
asymptotics. -/

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
      · omega
    have hcard' : Fintype.card (RoutingEdge (M i) (d i)) ≤
        (4 * M i) ^ (d i + 1) := hcard.trans hpow
    simp only [one_mul]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card (RoutingEdge (M i) (d i)) by
        positivity),
      Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ ((4 * M i) ^ (d i + 1) : ℕ) by
        positivity)]
    exact_mod_cast hcard'
  have hsmall := hbig.trans_isLittleO hcoef
  simpa [M, d] using hsmall

theorem variableStableGapExplicit_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => ((linearStableGap
      (Fintype.card (RoutingEdge
        (variableBranching p (D i))
        (variableDepth p (variableBranching p (D i))))) p : ℕ) : ℝ)) =o[l] U := by
  have hE : (fun i => (Fintype.card (RoutingEdge
      (variableBranching p (D i))
      (variableDepth p (variableBranching p (D i)))) : ℝ)) =o[l] U :=
    variableRoutingEdgeCard_littleO p hp hp₁ D U hU hD₁ hD
  exact linearStableGap_littleO_of_edge_littleO p hp _ U hU hE

end ErdosSimilarityGrowingGaps
