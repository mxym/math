import ErdosSimilarityGrowingGaps.AsymptoticProducts
import ErdosSimilarityGrowingGaps.VariableSpanBounds
namespace ErdosSimilarityGrowingGaps
open Filter Topology Asymptotics

/-- The squared length coefficient is dominated by the squared edge-envelope
used by the variable schedule. -/
theorem late_length_coefficient_sq_littleO
    {ι : Type*} {l : Filter ι} (K : ℕ) (hK : 2 ≤ K)
    (p σ : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1) (hσ : 0 < σ)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => ((((4 * lateBranching K p σ (D i)) ^
      lateDepth K p σ (D i) : ℕ) : ℝ) ^ 2)) =o[l] U := by
  have hDsum : (fun i => σ + D i) =o[l]
      (fun i => Real.log (Real.log (U i))) := by
    have hc : (fun _ : ι => σ) =o[l]
        (fun i => Real.log (Real.log (U i))) := by
      exact (isLittleO_const_id_atTop σ).comp_tendsto
        (tendsto_log_log_atTop_of_tendsto U hU)
    convert hc.add hD using 1 <;> ext i <;> ring
  have hDsum₁ : ∀ᶠ i in l, 1 ≤ σ + D i := by
    filter_upwards [hD₁] with i hi
    linarith
  have hpk : 0 < p / (K : ℝ) := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    positivity
  have hpk₁ : p / (K : ℝ) ≤ 1 := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    apply (div_le_iff₀ hKpos).2
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    nlinarith [hp₁]
  have hB := variable_eighth_power_squared_littleO
    (p / (K : ℝ)) hpk hpk₁ (fun i => σ + D i) U hU hDsum₁ hDsum
  have hB' : (fun i =>
      ((((8 * lateBranching K p σ (D i)) ^
        (lateDepth K p σ (D i) + 1) : ℕ) : ℝ) ^ 2)) =o[l] U := by
    simpa [lateBranching, lateDepth] using hB
  apply IsLittleO.of_bound
  intro c hc
  have hsmall := hB'.bound hc
  have hUn := hU.eventually (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hsmall, hD₁, hUn] with i hi hDi hUi
  have hM : 2 ≤ lateBranching K p σ (D i) :=
    lateBranching_ge_two K p σ (D i)
  have hd : 0 < lateDepth K p σ (D i) :=
    lateDepth_pos K hK p σ (D i) hp hp₁ hσ (by linarith)
  have hnat : (4 * lateBranching K p σ (D i)) ^
      lateDepth K p σ (D i) ≤
      (8 * lateBranching K p σ (D i)) ^
        (lateDepth K p σ (D i) + 1) := by
    calc
      _ ≤ (8 * lateBranching K p σ (D i)) ^
          lateDepth K p σ (D i) := by
            apply Nat.pow_le_pow_left
            omega
      _ ≤ _ := by
        exact Nat.pow_le_pow_right (by omega) (by omega)
  have hnat' : ((4 * lateBranching K p σ (D i)) ^
      lateDepth K p σ (D i) : ℝ) ≤
      (((8 * lateBranching K p σ (D i)) ^
        (lateDepth K p σ (D i) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤
      ((4 * lateBranching K p σ (D i)) ^ lateDepth K p σ (D i) : ℝ))
      (by positivity : 0 ≤
      (((8 * lateBranching K p σ (D i)) ^
        (lateDepth K p σ (D i) + 1) : ℕ) : ℝ))).2 hnat'
  have hnormA : ‖(((4 * lateBranching K p σ (D i)) ^
      lateDepth K p σ (D i) : ℕ) : ℝ)^2‖ =
      (((4 * lateBranching K p σ (D i)) ^
        lateDepth K p σ (D i) : ℕ) : ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnormB : ‖(((8 * lateBranching K p σ (D i)) ^
      (lateDepth K p σ (D i) + 1) : ℕ) : ℝ)^2‖ =
      (((8 * lateBranching K p σ (D i)) ^
        (lateDepth K p σ (D i) + 1) : ℕ) : ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnormU : ‖U i‖ = U i := by
    rw [Real.norm_eq_abs, abs_of_nonneg hUi]
  have hi' : ((((8 * lateBranching K p σ (D i)) ^
      (lateDepth K p σ (D i) + 1) : ℕ) : ℝ)^2) ≤ c * U i := by
    rw [hnormB] at hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hi
  rw [hnormA, hnormU]
  simpa [Nat.cast_pow, Nat.cast_mul] using hsq.trans hi'

end ErdosSimilarityGrowingGaps
