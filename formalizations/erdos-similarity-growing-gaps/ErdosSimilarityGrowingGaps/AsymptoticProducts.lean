import ErdosSimilarityGrowingGaps.VariableLengthSelection
namespace ErdosSimilarityGrowingGaps
open Filter Topology Asymptotics

/-- A product of two nonnegative quantities is little-o whenever the two
squares are little-o.  This is the AM-GM estimate used for variable routing
lengths. -/
theorem littleO_mul_of_sq
    {ι : Type*} {l : Filter ι} (A B U : ι → ℝ)
    (hA : (fun i => (A i)^2) =o[l] U)
    (hB : (fun i => (B i)^2) =o[l] U)
    (hAn : ∀ᶠ i in l, 0 ≤ A i) (hBn : ∀ᶠ i in l, 0 ≤ B i)
    (hUn : ∀ᶠ i in l, 0 ≤ U i) :
    (fun i => A i * B i) =o[l] U := by
  apply IsLittleO.of_bound
  intro c hc
  have hA' := hA.bound (by linarith : 0 < c / 2)
  have hB' := hB.bound (by linarith : 0 < c / 2)
  filter_upwards [hA', hB', hAn, hBn, hUn] with i ha hb hAi hBi hUi
  have hsq : 2 * (A i * B i) ≤ (A i)^2 + (B i)^2 := by
    nlinarith [sq_nonneg (A i - B i)]
  have ha' : (A i)^2 ≤ (c / 2) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A i)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using ha
  have hb' : (B i)^2 ≤ (c / 2) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (B i)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hb
  have hp : 0 ≤ A i * B i := mul_nonneg hAi hBi
  rw [Real.norm_eq_abs, abs_of_nonneg hp,
    Real.norm_eq_abs, abs_of_nonneg hUi]
  nlinarith

/-- The shifted logarithm has a square which is little-o of its argument. -/
theorem shifted_log_sq_littleO
    {ι : Type*} {l : Filter ι} (U : ι → ℝ)
    (hU : Tendsto U l atTop) :
    (fun i => (Real.log (U i + 2))^2) =o[l] U := by
  have hbase : (fun i => (Real.log (U i))^2) =o[l] U := by
    simpa [Function.comp_def] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto hU)
  apply IsLittleO.of_bound
  intro c hc
  have hbase' := hbase.bound (by linarith : 0 < c / 4)
  have hlarge : ∀ᶠ i in l, 2 ≤ U i := hU.eventually_ge_atTop 2
  filter_upwards [hbase', hlarge] with i hi hUi
  have hUi0 : 0 < U i := by linarith
  have hsum : 0 ≤ Real.log (U i + 2) :=
    Real.log_nonneg (by linarith)
  have hlog : Real.log (U i + 2) ≤ 2 * Real.log (U i) := by
    have hquad : U i + 2 ≤ U i * U i := by nlinarith [sq_nonneg (U i - 1)]
    have hlog' := Real.log_le_log (by linarith) hquad
    rw [Real.log_mul hUi0.ne' hUi0.ne'] at hlog'
    nlinarith
  have hsq : (Real.log (U i + 2))^2 ≤ 4 * (Real.log (U i))^2 := by
    nlinarith [sq_nonneg (Real.log (U i + 2) - 2 * Real.log (U i))]
  have hi' : (Real.log (U i))^2 ≤ (c / 4) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (U i))),
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ U i), mul_one] using hi
  have hnormS : ‖(Real.log (U i + 2))^2‖ =
      (Real.log (U i + 2))^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnormU : ‖U i‖ = U i := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnormS, hnormU]
  nlinarith [hsq, hi']

end ErdosSimilarityGrowingGaps
