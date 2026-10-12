import ErdosSimilarityGrowingGaps.VariableLengthSelection

namespace ErdosSimilarityGrowingGaps
open Filter Topology Asymptotics

/-- The joint length selector remains valid with any fixed positive fraction of
its origin as the available affine-span budget. -/
theorem eventually_exists_joint_template_length_scaled
    {ι : Type*} {l : Filter ι}
    (A : ι → ℝ) (P : ι → ℕ) (B U : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hU : Tendsto U l atTop)
    (hA_nonneg : ∀ᶠ i in l, 0 ≤ A i)
    (hB_nonneg : ∀ᶠ i in l, 0 ≤ B i)
    (hAP : (fun i => A i * (P i : ℝ)) =o[l] U)
    (hALog : (fun i => A i * (4 * Real.log (U i + 2))) =o[l] U)
    (hA : A =o[l] U)
    (hB : B =o[l] U) :
    ∀ᶠ i in l, ∃ L : ℕ,
      P i ≤ L ∧ A i * (L : ℝ) + B i ≤ t * U i := by
  have hUt : Tendsto (fun i => t * U i) l atTop := hU.const_mul_atTop ht
  have hAPt : (fun i => A i * (P i : ℝ)) =o[l]
      (fun i => t * U i) := by
    simpa [Function.comp_def, mul_comm] using hAP.const_mul_right (ne_of_gt ht)
  have hALogt : (fun i => A i * (4 * Real.log (t * U i + 2))) =o[l]
      (fun i => t * U i) := by
    apply IsLittleO.of_bound
    intro c hc
    let Clog : ℝ := Real.log (t + 2)
    have hClog : 0 ≤ Clog := by
      dsimp [Clog]
      exact Real.log_nonneg (by linarith)
    have hden : 0 < 2 * (1 + 4 * Clog) := by positivity
    have heps : 0 < c * t / (2 * (1 + 4 * Clog)) := by positivity
    have hsL := hALog.bound heps
    have hsA := hA.bound heps
    have hlarge := hU.eventually_ge_atTop (max 1 (2 / t))
    filter_upwards [hsL, hsA, hlarge, hA_nonneg] with i hiL hiA hUi hAi
    have hUi0 : 0 ≤ U i := by
      exact (show (0 : ℝ) ≤ 1 by norm_num).trans
        ((le_max_left 1 (2 / t)).trans hUi)
    have hlogU : 0 ≤ Real.log (U i + 2) := Real.log_nonneg (by linarith)
    have harg : t * U i + 2 ≤ (t + 2) * (U i + 2) := by nlinarith
    have hlogarg : Real.log (t * U i + 2) ≤ Clog + Real.log (U i + 2) := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < t * U i + 2) harg
      have ht2 : t + 2 ≠ 0 := by positivity
      have hUi2 : U i + 2 ≠ 0 := by positivity
      rw [Real.log_mul ht2 hUi2] at hh
      exact hh
    have hL : A i * (4 * Real.log (U i + 2)) ≤
        (c * t / (2 * (1 + 4 * Clog))) * U i := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hAi
        (by positivity : 0 ≤ 4 * Real.log (U i + 2))),
        Real.norm_eq_abs, abs_of_nonneg hUi0, mul_one] using hiL
    have hA : A i ≤
        (c * t / (2 * (1 + 4 * Clog))) * U i := by
      have hiA' : A i ≤ (c * t / (2 * (1 + 4 * Clog))) * U i := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hAi,
          Real.norm_eq_abs, abs_of_nonneg hUi0, mul_one] using hiA
      exact hiA'
    have hAconst := mul_le_mul_of_nonneg_left hA
      (by positivity : 0 ≤ 4 * Clog)
    have hmain : A i * (4 * Real.log (t * U i + 2)) ≤
        (c * t / 2) * U i := by
      have hmul := mul_le_mul_of_nonneg_left hlogarg
        (by positivity : 0 ≤ 4 * A i)
      calc
        A i * (4 * Real.log (t * U i + 2)) ≤
            A i * (4 * Clog + 4 * Real.log (U i + 2)) := by
              nlinarith [hmul]
        _ = 4 * Clog * A i + A i * (4 * Real.log (U i + 2)) := by ring
        _ ≤ 4 * Clog * ((c * t / (2 * (1 + 4 * Clog))) * U i) +
              (c * t / (2 * (1 + 4 * Clog))) * U i := by
              exact add_le_add hAconst hL
        _ = (c * t / 2) * U i := by
              field_simp
              ring
    have htarget : A i * (4 * Real.log (t * U i + 2)) ≤ c * (t * U i) := by
      have hhalf : 0 ≤ (c * t / 2) * U i := by positivity
      nlinarith [hmain, hhalf]
    have hlogt : 0 ≤ Real.log (t * U i + 2) :=
      Real.log_nonneg (by nlinarith [hUi0])
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hAi
        (by positivity : 0 ≤ 4 * Real.log (t * U i + 2))),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hUi0), mul_one] using htarget
  have hAt : A =o[l] (fun i => t * U i) := by
    simpa [Function.comp_def, mul_comm] using hA.const_mul_right (ne_of_gt ht)
  have hBt : B =o[l] (fun i => t * U i) := by
    simpa [Function.comp_def, mul_comm] using hB.const_mul_right (ne_of_gt ht)
  exact eventually_exists_joint_template_length A P B (fun i => t * U i)
    hUt hA_nonneg hB_nonneg hAPt hALogt hAt hBt

end ErdosSimilarityGrowingGaps
