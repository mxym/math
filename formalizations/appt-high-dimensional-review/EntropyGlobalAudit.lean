import APPTReview.EntropyGlobalControls
import Verification.ReplaySupport

run_cmd (APPTVerification.replayAndCorrupt [
  ``APPTReview.appt_entropy_saturation_iff_flat_purity,
  ``APPTReview.baseline_graph_head_budget,
  ``APPTReview.scalar_head_variance_bound,
  ``APPTReview.strictMono_fin_val_lower,
  ``APPTReview.rowRank_first_row_lower,
  ``APPTReview.residual_first_row_le_head,
  ``APPTReview.density_appt_head_retained_variance,
  ``APPTReview.pairedPivot_eq_paperPivot,
  ``APPTReview.density_appt_normalized_head_variance,
  ``APPTReview.entropy_head_corrected_variance,
  ``APPTReview.density_appt_entropy_corrected_variance,
  ``APPTReview.scaled_entropyKernel,
  ``APPTReview.spectrum_entropy_centering,
  ``APPTReview.spectrum_quadratic_centering,
  ``APPTReview.spectrum_entropy_remainder_identity,
  ``APPTReview.interval_zero_minimum,
  ``APPTReview.entropyKernel_hasDerivAt,
  ``APPTReview.entropyKernel_quadratic_bounds,
  ``APPTReview.entropyRemainder_bounds,
  ``APPTReview.entropy_bulk_partition,
  ``APPTReview.entropy_remainder_partition,
  ``APPTReview.density_appt_full_entropy_rest_bound,
  ``APPTReview.entropy_rest_taylor_bound,
  ``APPTReview.density_appt_full_entropy_taylor_bound,
  ``APPTReview.ordered_low_pivot_variance,
  ``APPTReview.ordered_two_sided_pivot_variance,
  ``APPTReview.ordered_normalized_moment_budget,
  ``APPTReview.paper_pivot_quarter_bounds,
  ``APPTReview.density_appt_entropy_normalization_budget,
  ``APPTReview.antitone_nonnegative_prefix_square,
  ``APPTReview.sorted_bulk_deviation_square,
  ``APPTReview.density_appt_entropy_bulk_smallness,
  ``APPTReview.entropyVarianceCap_nonneg,
  ``APPTReview.density_appt_entropy_mean_smallness,
  ``APPTReview.density_appt_dimension_entropy_bound,
  ``APPTReview.entropy_dimension_limits,
  ``APPTReview.paperNormalization_pos,
  ``APPTReview.entropy_deficit_normalization,
  ``APPTReview.appt_paperNormalization_tendsto,
  ``APPTReview.entropy_tail_cap_identity,
  ``APPTReview.appt_vonNeumann_fixed_aspect_upper,
  ``APPTReview.appt_full_entropy_head_saturation,
  ``APPTReview.appt_full_entropy_saturation_flat,
  ``APPTReview.density_flat_entropy_purity_bounds,
  ``APPTReview.flat_purity_to_entropy_error,
  ``APPTReview.flat_entropy_to_purity_error,
  ``APPTReview.stateExcessPurity_nonneg,
  ``APPTReview.flat_density_entropy_purity_limit_iff,
  ``APPTReview.entropy_taylor_radius_one_rejected,
  ``APPTReview.retained_head_cannot_be_deleted,
  ``APPTReview.entropy_nonuniform_pivot_control,
  ``APPTReview.entropy_bulk_partition_control,
  ``APPTReview.entropy_zero_remainder_control
  ] "entropy-global-kernel")

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.appt_full_entropy_saturation_flat "entropy-global-control-0"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.appt_full_entropy_head_saturation "entropy-global-control-1"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.appt_vonNeumann_fixed_aspect_upper "entropy-global-control-2"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.density_appt_dimension_entropy_bound "entropy-global-control-3"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.density_appt_head_retained_variance "entropy-global-control-4"

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.spectrum_entropy_centering "entropy-global-control-5"
