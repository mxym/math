import RankSupport
import RankSupportVerification.ReplaySupport

run_cmd (RankSupportVerification.replayAndCorrupt [
  ``ExtractionRankSupport.exact_rankBounded_iid_effect_mul_rankBudgetProjector,
  ``ExtractionRankSupport.productVector_mem_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetSpace_mono,
  ``ExtractionRankSupport.constant_factors_span_finrank_le_one,
  ``ExtractionRankSupport.purePower_mem_rankBudgetSpace,
  ``ExtractionRankSupport.symmetric_range_le_rankBudgetSpace,
  ``ExtractionRankSupport.productVector_factors_smul,
  ``ExtractionRankSupport.rank_one_productVector_mem_symmetric_range,
  ``ExtractionRankSupport.rankBudgetSpace_one_eq_symmetric_range,
  ``ExtractionRankSupport.psd_mul_eq_zero_of_trace_re_eq_zero,
  ``ExtractionRankSupport.exact_density_effect_fixes_density,
  ``ExtractionRankSupport.tensorMatrix_mulVec_productVector,
  ``ExtractionRankSupport.transformed_factors_finrank_le,
  ``ExtractionRankSupport.tensorMatrix_preserves_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetProjector_tensorMatrix_compress,
  ``ExtractionRankSupport.rankBudgetProjector_commutes_tensorMatrix,
  ``ExtractionRankSupport.hermitian_projection_trace_eq_rank,
  ``ExtractionRankSupport.normalizedProjection_density,
  ``ExtractionRankSupport.normalizedProjection_rank_le,
  ``ExtractionRankSupport.tensorMatrix_real_smul,
  ``ExtractionRankSupport.tensorMatrix_range_le_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetSpace_eq_densityTensorSpace,
  ``ExtractionRankSupport.fixes_densityTensor_mul_rankBudgetProjector,
  ``ExtractionRankSupport.symmetric_rank_le_rankBudgetProjector_rank,
  ``ExtractionRankSupport.rankBudgetProjector_rank_mono,
  ``ExtractionRankSupport.rankBudgetProjector_rank_pos,
  ``ExtractionRankSupport.rankBudgetProjector_rank_le_dimension,
  ``ExtractionRankSupport.rankBudgetProjector_rank_one_choose,
  ``ExtractionRankSupport.rankBudgetProjector_rank_eq_dimension,
  ``ExtractionRankSupport.tensorMatrix_col_mem_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetProjector_properties,
  ``ExtractionRankSupport.rankBudgetProjector_isHermitian,
  ``ExtractionRankSupport.rankBudgetProjector_idempotent,
  ``ExtractionRankSupport.rankBudgetProjector_range,
  ``ExtractionRankSupport.rankBudgetProjector_rank,
  ``ExtractionRankSupport.rankBudgetProjector_fixes,
  ``ExtractionRankSupport.rankBudgetProjector_posSemidef,
  ``ExtractionRankSupport.matrix_mul_eq_of_fixes_columns,
  ``ExtractionRankSupport.rankBudgetProjector_mul_tensorMatrix,
  ``ExtractionRankSupport.tensorMatrix_mul_rankBudgetProjector,
  ``ExtractionRankSupport.rankBudgetProjector_tensorMatrix_support,
  ``ExtractionRankSupport.rankBudgetProjector_density_support,
  ``ExtractionRankSupport.rankBudgetProjector_one_eq_symmetricProjector,
  ``ExtractionRankSupport.rankBudgetProjector_eq_one_of_dimension_le
] "verification/rank-kernel")

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetSpace_eq_densityTensorSpace "verification/rank-control-1"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_one_eq_symmetricProjector "verification/rank-control-2"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_commutes_tensorMatrix "verification/rank-control-3"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_density_support "verification/rank-control-4"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.psd_mul_eq_zero_of_trace_re_eq_zero "verification/rank-control-5"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_rank_pos "verification/rank-control-6"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_eq_one_of_dimension_le "verification/rank-control-7"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.tensorMatrix_mulVec_productVector "verification/rank-control-8"
