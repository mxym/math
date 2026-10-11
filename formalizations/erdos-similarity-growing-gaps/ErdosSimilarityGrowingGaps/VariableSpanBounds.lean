import ErdosSimilarityGrowingGaps.VariableProductBounds
import ErdosSimilarityGrowingGaps.VariableGapBounds

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The gap term in the affine span is sublinear.  The squared power estimate
is proved separately because multiplying two `o(U)` terms would not suffice. -/
theorem lateRoutingGapProduct_littleO
    {ι : Type*} {l : Filter ι}
    (K : ℕ) (hK : 2 ≤ K) (p δ : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (hδ : 0 < δ)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i =>
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) *
        (lateStableGapExplicit K p δ (D i) : ℝ)) =o[l] U := by
  have hKr : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hpk : 0 < p / (K : ℝ) := by positivity
  have hpk₁ : p / (K : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hKr).2
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have hpK : p ≤ (K : ℝ) := by
      calc
        p ≤ 1 := hp₁
        _ ≤ K := hKreal
    simpa only [one_mul] using hpK
  have hLL : Tendsto (fun i => Real.log (Real.log (U i))) l atTop :=
    tendsto_log_log_atTop_of_tendsto U hU
  have hconst : (fun _ : ι => δ) =o[l]
      (fun i => Real.log (Real.log (U i))) := by
    exact (isLittleO_const_id_atTop δ).comp_tendsto hLL
  have hDsum : (fun i => δ + D i) =o[l]
      (fun i => Real.log (Real.log (U i))) := by
    have h := hconst.add hD
    convert h using 1 <;> ext i <;> ring
  have hDsum₁ : ∀ᶠ i in l, 1 ≤ δ + D i := by
    filter_upwards [hD₁] with i hi
    linarith
  have hP2 := variable_eighth_power_squared_littleO
    (p / (K : ℝ)) hpk hpk₁ (fun i => δ + D i) U hU hDsum₁ hDsum
  have hP2' : (fun i =>
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) ^ 2) =o[l] U := by
    simpa [lateBranching, lateDepth] using hP2
  have hU₀ : ∀ᶠ i in l, 0 ≤ U i :=
    hU.eventually (eventually_ge_atTop (0 : ℝ))
  let P : ι → ℝ := fun i =>
    (((8 * lateBranching K p δ (D i)) ^
      (lateDepth K p δ (D i) + 1) : ℕ) : ℝ)
  let G : ι → ℝ := fun i =>
    (lateStableGapExplicit K p δ (D i) : ℝ)
  have hP2'' : (fun i => (P i) ^ 2) =o[l] U := by
    simpa [P] using hP2'
  have hPnonneg : ∀ᶠ i in l, 0 ≤ P i := by
    filter_upwards [] with i
    dsimp [P]
    positivity
  have hPone : ∀ᶠ i in l, 1 ≤ P i := by
    filter_upwards [] with i
    dsimp [P]
    have hM : 2 ≤ lateBranching K p δ (D i) :=
      lateBranching_ge_two K p δ (D i)
    have hbase : 1 ≤ 8 * lateBranching K p δ (D i) := by omega
    exact_mod_cast (Nat.one_le_pow _ _ hbase)
  have hbound : ∀ᶠ i in l, G i ≤ (8 / p + 1) * P i := by
    filter_upwards [] with i
    dsimp [G, P]
    have hM : 2 ≤ lateBranching K p δ (D i) :=
      lateBranching_ge_two K p δ (D i)
    have hcard := routingEdge_card_le_pow
      (lateBranching K p δ (D i)) (lateDepth K p δ (D i)) hM
    have hpow : (2 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) ≤
        (8 * lateBranching K p δ (D i)) ^
          (lateDepth K p δ (D i) + 1) := by
      apply Nat.pow_le_pow_left
      omega
    have hcard' : Fintype.card (RoutingEdge
        (lateBranching K p δ (D i))
        (lateDepth K p δ (D i))) ≤
        (8 * lateBranching K p δ (D i)) ^
          (lateDepth K p δ (D i) + 1) := hcard.trans hpow
    have hcardR : (Fintype.card (RoutingEdge
        (lateBranching K p δ (D i))
        (lateDepth K p δ (D i))) : ℝ) ≤
        ((8 * lateBranching K p δ (D i)) ^
          (lateDepth K p δ (D i) + 1) : ℕ) := by
      exact_mod_cast hcard'
    have hgap := lateStableGapExplicit_upper K p δ (D i) hp
    have hgap' : G i ≤ 8 / p * P i + 1 := by
      calc
        G i ≤ 8 * (Fintype.card (RoutingEdge
          (lateBranching K p δ (D i))
          (lateDepth K p δ (D i))) : ℝ) / p + 1 := hgap
        _ ≤ 8 / p * P i + 1 := by
          have hcoef : 8 * (Fintype.card (RoutingEdge
              (lateBranching K p δ (D i))
              (lateDepth K p δ (D i))) : ℝ) / p ≤ 8 / p * P i := by
            have hm := mul_le_mul_of_nonneg_left hcardR
              (show 0 ≤ 8 / p by positivity)
            have hcardRP :
                (Fintype.card (RoutingEdge
                  (lateBranching K p δ (D i))
                  (lateDepth K p δ (D i))) : ℝ) ≤ P i := by
              simpa [P] using hcardR
            have hm' := mul_le_mul_of_nonneg_left hcardRP
              (show 0 ≤ 8 / p by positivity)
            calc
              8 * (Fintype.card (RoutingEdge
                (lateBranching K p δ (D i))
                (lateDepth K p δ (D i))) : ℝ) / p =
                  8 / p * (Fintype.card (RoutingEdge
                    (lateBranching K p δ (D i))
                    (lateDepth K p δ (D i))) : ℝ) := by ring
              _ ≤ 8 / p * P i := hm'
          nlinarith [hcoef]
    have hP1 : 1 ≤ P i := by
      dsimp [P]
      have hbase : 1 ≤ 8 * lateBranching K p δ (D i) := by omega
      exact_mod_cast (Nat.one_le_pow _ _ hbase)
    have hC : 0 ≤ 8 / p := by positivity
    have hPmul : P i ≤ (P i) ^ 2 := by nlinarith
    calc
      G i ≤ 8 / p * P i + 1 := hgap'
      _ ≤ (8 / p + 1) * P i := by nlinarith
  apply IsLittleO.of_bound
  intro c hc
  have hC : 0 < 8 / p + 1 := by positivity
  have hc' : 0 < c / (8 / p + 1) := by positivity
  have hsmall := hP2''.bound hc'
  filter_upwards [hsmall, hU₀, hPnonneg, hPone, hbound] with
      i hi hUi hPi hP1 hGi
  have hP2norm : (P i) ^ 2 ≤ (c / (8 / p + 1)) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (P i)),
      abs_of_nonneg hUi, mul_one] using hi
  have hprod : P i * G i ≤ (8 / p + 1) * (P i) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hGi hPi
    have hPmul : P i ≤ (P i) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hPmul (show 0 ≤ 8 / p by positivity)]
  have hprod' : P i * G i ≤ c * U i := by
    have hmul := mul_le_mul_of_nonneg_left hP2norm hC.le
    calc
      P i * G i ≤ (8 / p + 1) * (P i) ^ 2 := hprod
      _ ≤ (8 / p + 1) * ((c / (8 / p + 1)) * U i) := hmul
      _ = c * U i := by field_simp
  have hprod_nonneg : 0 ≤ P i * G i := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hUi]
  exact hprod'

end ErdosSimilarityGrowingGaps
