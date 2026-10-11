import ErdosSimilarityGrowingGaps.VariableScheduleAsymptotics
import ErdosSimilarityGrowingGaps.VariableEntropyLength
import ErdosSimilarityGrowingGaps.WindowFillingAsymptotics
import ErdosSimilarityGrowingGaps.VariableLengthSelection

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-- Along every WindowFilling sequence, one can choose a base length that is
large enough for both the mandatory local budget and the entropy budget while
remaining below the origin after multiplication by the routing coefficient. -/
theorem eventually_late_template_length_selection
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (p σ : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1) (hσ : 0 < σ)
    (U : ℕ → ℕ) (D : ℕ → ℝ)
    (hUtend : Tendsto (fun j => (U j : ℝ)) atTop atTop)
    (hUlog : ∀ j, 1 < Real.log (U j : ℝ))
    (hUfill : ∀ j, FillsAnnulus Z (U j) (4 * K) (D j))
    (hD : D =o[atTop] (fun j => Real.log (Real.log (U j : ℝ)))) :
    ∀ᶠ j : ℕ in atTop,
      ∃ L : ℕ,
        Nat.ceil (2 * ((K : ℝ) * (σ + D j))) ≤ L ∧
        variableEntropyLength p (lateBranching K p σ (D j)) (U j) ≤ L ∧
        (((4 * lateBranching K p σ (D j)) ^
          lateDepth K p σ (D j) : ℕ) : ℝ) * (L : ℝ) +
          (((8 * lateBranching K p σ (D j)) ^
            (lateDepth K p σ (D j) + 1) : ℕ) : ℝ) *
            (lateStableGapExplicit K p σ (D j) : ℝ) ≤ (U j : ℝ) := by
  have hD₁ : ∀ᶠ j : ℕ in atTop, 1 ≤ D j := by
    filter_upwards [] with j
    exact (hUfill j).2.2.1
  have hD₀ : ∀ᶠ j : ℕ in atTop, 0 ≤ D j := by
    filter_upwards [hD₁] with j hj
    linarith
  let A : ℕ → ℝ := fun j =>
    (((4 * lateBranching K p σ (D j)) ^
      lateDepth K p σ (D j) : ℕ) : ℝ)
  let E : ℕ → ℝ := fun j =>
    (((8 * lateBranching K p σ (D j)) ^
      (lateDepth K p σ (D j) + 1) : ℕ) : ℝ)
  let B : ℕ → ℝ := fun j =>
    E j * (lateStableGapExplicit K p σ (D j) : ℝ)
  let P₀ : ℕ → ℕ := fun j =>
    Nat.ceil (2 * ((K : ℝ) * (σ + D j))) + 1
  let P₁ : ℕ → ℕ := fun j =>
    variableEntropyLength p (lateBranching K p σ (D j)) (U j)
  have hA2 : (fun j => (A j)^2) =o[atTop]
      (fun j => (U j : ℝ)) := by
    simpa [A] using late_length_coefficient_sq_littleO K hK p σ hp hp₁ hσ D
      (fun j => (U j : ℝ)) hUtend hD₁ hD
  have hM2 : (fun j => (lateBranching K p σ (D j) : ℝ)^2) =o[atTop]
      (fun j => (U j : ℝ)) := by
    apply IsLittleO.of_bound
    intro c hc
    have hs := hA2.bound hc
    filter_upwards [hs, hD₁] with j hj hDj
    have hM : 2 ≤ lateBranching K p σ (D j) := lateBranching_ge_two K p σ (D j)
    have hd : 0 < lateDepth K p σ (D j) :=
      lateDepth_pos K hK p σ (D j) hp hp₁ hσ (by linarith [hDj])
    have hpow : lateBranching K p σ (D j) ≤
        (4 * lateBranching K p σ (D j)) ^ lateDepth K p σ (D j) := by
      calc
        lateBranching K p σ (D j) ≤
            lateBranching K p σ (D j) ^ lateDepth K p σ (D j) := by
              exact Nat.le_pow (a := lateBranching K p σ (D j))
                (b := lateDepth K p σ (D j)) (by omega)
        _ ≤ (4 * lateBranching K p σ (D j)) ^ lateDepth K p σ (D j) := by
              apply Nat.pow_le_pow_left
              omega
    have hpowR : (lateBranching K p σ (D j) : ℝ) ≤ A j := by
      dsimp [A]; exact_mod_cast hpow
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (lateBranching K p σ (D j) : ℝ))
      (by positivity : 0 ≤ A j)).2 hpowR
    have hi : A j ^ 2 ≤ c * (U j : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A j)),
        Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ U j), mul_one] using hj
    have hMi : (lateBranching K p σ (D j) : ℝ)^2 ≤ c * (U j : ℝ) := hsq.trans hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (lateBranching K p σ (D j) : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ U j), mul_one] using hMi
  have hP₁2 : (fun j => (P₁ j : ℝ)^2) =o[atTop]
      (fun j => (U j : ℝ)) := by
    dsimp [P₁]
    exact variableEntropyLength_sq_littleO p _ U hUtend hM2
  have hAP₀ : (fun j => A j * (P₀ j : ℝ)) =o[atTop]
      (fun j => (U j : ℝ)) := by
    dsimp [P₀]
    exact late_length_coefficient_mul_base_budget_littleO K hK p σ hp hp₁ hσ D (fun j => (U j : ℝ)) hUtend hD₁ hD
  have hAP₁ : (fun j => A j * (P₁ j : ℝ)) =o[atTop]
      (fun j => (U j : ℝ)) := by
    apply littleO_mul_of_sq A (fun j => (P₁ j : ℝ)) (fun j => (U j : ℝ)) hA2 hP₁2
    · filter_upwards [] with j; positivity
    · filter_upwards [] with j; positivity
    · exact hUtend.eventually (eventually_ge_atTop 0)
  have hAP : (fun j => A j * ((P₀ j + P₁ j : ℕ) : ℝ)) =o[atTop]
      (fun j => (U j : ℝ)) := by
    have h := hAP₀.add hAP₁
    convert h using 1 <;> ext j <;> push_cast <;> ring
  have hALog : (fun j => A j * (4 * Real.log ((U j : ℝ) + 2))) =o[atTop]
      (fun j => (U j : ℝ)) :=
    late_length_coefficient_mul_shifted_log_littleO K hK p σ hp hp₁ hσ D (fun j => (U j : ℝ)) hUtend hD₁ hD
  have hA : A =o[atTop] (fun j => (U j : ℝ)) := by
    apply littleO_of_sq_of_one_le A (fun j => (U j : ℝ)) hA2
    filter_upwards [hD₀] with j hDj
    have hM : 2 ≤ lateBranching K p σ (D j) := lateBranching_ge_two K p σ (D j)
    have hd : 0 < lateDepth K p σ (D j) :=
      lateDepth_pos K hK p σ (D j) hp hp₁ hσ (by linarith [hDj])
    dsimp [A]
    exact_mod_cast (Nat.one_le_pow _ _ (by omega))
    · exact hUtend.eventually (eventually_ge_atTop 0)
  have hB : B =o[atTop] (fun j => (U j : ℝ)) := by
    dsimp [B, E]
    exact lateRoutingGapProduct_littleO K hK p σ hp hp₁ hσ D (fun j => (U j : ℝ)) hUtend hD₁ hD
  have hB0 : ∀ᶠ j : ℕ in atTop, 0 ≤ B j := by
    filter_upwards [] with j; positivity
  have hA0 : ∀ᶠ j : ℕ in atTop, 0 ≤ A j := by
    filter_upwards [] with j; positivity
  have hU0 : ∀ᶠ j : ℕ in atTop, 0 ≤ (U j : ℝ) := hUtend.eventually (eventually_ge_atTop 0)
  have hev := eventually_exists_joint_template_length A (fun j => P₀ j + P₁ j) B
    (fun j => (U j : ℝ)) hUtend hA0 hB0 hAP hALog hA hB
  filter_upwards [hev] with j hj
  obtain ⟨L, hPL, hspan⟩ := hj
  refine ⟨L, ?_, ?_, ?_⟩
  · have hp0 : Nat.ceil (2 * ((K : ℝ) * (σ + D j))) ≤ P₀ j := by
      dsimp [P₀]
      omega
    exact hp0.trans ((Nat.le_add_right _ _).trans hPL)
  · exact le_trans (Nat.le_add_left _ _) hPL
  · exact hspan

end ErdosSimilarityGrowingGaps
