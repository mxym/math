import ErdosSimilarityGrowingGaps.Sampling

namespace ErdosSimilarityGrowingGaps

lemma loglog_mul_le_two
    {R U : ℝ} (hR : 2 ≤ R) (hU : 1 < U)
    (hRlog : Real.log R ≤ Real.log U)
    (hll : Real.log 2 ≤ Real.log (Real.log U)) :
    Real.log (Real.log (R * U)) ≤ 2 * Real.log (Real.log U) := by
  have hRpos : 0 < R := by linarith
  have hUpos : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hlogRUpos : 0 < Real.log (R * U) := by
    apply Real.log_pos
    nlinarith [hR, hU]
  have hmul : Real.log (R * U) = Real.log R + Real.log U := by
    rw [Real.log_mul (ne_of_gt hRpos) (ne_of_gt hUpos)]
  have hlogRU_le : Real.log (R * U) ≤ 2 * Real.log U := by
    rw [hmul]
    linarith
  have htwo_pos : 0 < 2 * Real.log U := by positivity
  have hloglog_le : Real.log (Real.log (R * U)) ≤ Real.log (2 * Real.log U) := by
    exact (Real.strictMonoOn_log.monotoneOn hlogRUpos htwo_pos hlogRU_le)
  have hlogtwo : Real.log (2 * Real.log U) = Real.log 2 + Real.log (Real.log U) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogU)]
  rw [hlogtwo] at hloglog_le
  linarith

end ErdosSimilarityGrowingGaps
