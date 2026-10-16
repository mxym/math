import RankSupport
import RankSupportVerification.ReplaySupport

run_cmd (RankSupportVerification.replayAndCorrupt [
  ``ExtractionRankSupport.rankBudgetProjector_log_rank_per_copy_limit,
  ``ExtractionRankSupport.productVector_mem_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetSpace_mono,
  ``ExtractionRankSupport.constant_factors_span_finrank_le_one,
  ``ExtractionRankSupport.purePower_mem_rankBudgetSpace,
  ``ExtractionRankSupport.symmetric_range_le_rankBudgetSpace,
  ``ExtractionRankSupport.productVector_factors_smul,
  ``ExtractionRankSupport.rank_one_productVector_mem_symmetric_range,
  ``ExtractionRankSupport.rankBudgetSpace_one_eq_symmetric_range,
  ``ExtractionRankSupport.coordinateWordEmbedding_refl,
  ``ExtractionRankSupport.productVector_basis_word,
  ``ExtractionRankSupport.rankBudgetProjector_eq_one_of_blocklength_le,
  ``ExtractionRankSupport.psd_mul_eq_zero_of_trace_re_eq_zero,
  ``ExtractionRankSupport.exact_density_effect_fixes_density,
  ``ExtractionRankSupport.exact_rankBounded_iid_effect_mul_rankBudgetProjector,
  ``ExtractionRankSupport.symmetricProjector_rank_le_explicit_polynomial,
  ``ExtractionRankSupport.shifted_choose_le_explicit_polynomial,
  ``ExtractionRankSupport.symmetricProjector_log_rank_le_explicit,
  ``ExtractionRankSupport.coordinate_factors_finrank_le,
  ``ExtractionRankSupport.coordinate_productVector_eq_isometry_col,
  ``ExtractionRankSupport.rankBudgetProjector_rank_ge_power,
  ``ExtractionRankSupport.rectangularTensor_col_mem_rankBudgetSpace,
  ``ExtractionRankSupport.rectangularColumnSpace_le_rankBudgetSpace,
  ``ExtractionRankSupport.rankBudgetSpace_eq_rectangularUniversalSpace,
  ``ExtractionRankSupport.supportCoefficientMatrix_range,
  ``ExtractionRankSupport.rankBudgetProjector_rank_eq_coefficientMatrix_rank,
  ``ExtractionRankSupport.symmetric_log_rank_per_copy_limit,
  ``ExtractionRankSupport.rankBudgetProjector_rank_div_geometric_limit,
  ``ExtractionRankSupport.rankBudgetProjector_sqrt_rank_div_geometric_limit,
  ``ExtractionRankSupport.rankBudgetProjector_geometric_div_sqrt_rank_atTop,
  ``ExtractionRankSupport.isometry_factor_range,
  ``ExtractionRankSupport.exists_unitary_matrix_range_factors,
  ``ExtractionRankSupport.unitaryTensorOrbitSpace_eq_rankBudgetSpace,
  ``ExtractionRankSupport.fixed_density_unitary_conjugate_density,
  ``ExtractionRankSupport.exact_fixed_density_orbit_effect_mul_rankBudgetProjector,
  ``ExtractionRankSupport.coordinateRankProjection_isHermitian,
  ``ExtractionRankSupport.coordinateRankProjection_idempotent,
  ``ExtractionRankSupport.coordinateRankProjection_rank,
  ``ExtractionRankSupport.matrix_rank_real_smul_le,
  ``ExtractionRankSupport.flatCoordinateDensity_density,
  ``ExtractionRankSupport.flatCoordinateDensity_rank,
  ``ExtractionRankSupport.normalizedProjection_trace_square,
  ``ExtractionRankSupport.actual_tensorMatrix_trace,
  ``ExtractionRankSupport.flatCoordinateDensity_tensor_density,
  ``ExtractionRankSupport.flatCoordinateDensity_tensor_purity,
  ``ExtractionRankSupport.exists_flat_rank_density,
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
  ``ExtractionRankSupport.rectangularContraction_purePower,
  ``ExtractionRankSupport.rectangularTensor_col_mem_columnSpace,
  ``ExtractionRankSupport.finrank_rectangularColumnSpace_le,
  ``ExtractionRankSupport.rectangularTensor_col_mem_universalSpace,
  ``ExtractionRankSupport.finrank_finite_sup_rectangularColumnSpace_le,
  ``ExtractionRankSupport.finrank_rectangularUniversalSpace_le,
  ``ExtractionRankSupport.rectangularTensor_mulVec_productVector,
  ``ExtractionRankSupport.exists_rectangular_factorization,
  ``ExtractionRankSupport.rankBudgetSpace_le_rectangularUniversalSpace,
  ``ExtractionRankSupport.rankBudgetProjector_rank_le_polynomial,
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

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.exact_rankBounded_iid_effect_mul_rankBudgetProjector "verification/rank-control-9"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_rank_le_polynomial "verification/rank-control-10"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_rank_ge_power "verification/rank-control-11"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.rankBudgetProjector_geometric_div_sqrt_rank_atTop "verification/rank-control-12"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.supportCoefficientMatrix_range "verification/rank-control-13"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.symmetricProjector_log_rank_le_explicit "verification/rank-control-14"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.exact_fixed_density_orbit_effect_mul_rankBudgetProjector "verification/rank-control-15"

run_cmd RankSupportVerification.rejectCorruptTheorem ``ExtractionRankSupport.flatCoordinateDensity_tensor_purity "verification/rank-control-16"
