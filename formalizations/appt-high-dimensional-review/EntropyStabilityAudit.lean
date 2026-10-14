import APPTReview.EntropyStabilityControls
import Verification.ReplaySupport

run_cmd (APPTVerification.replayAndCorrupt [
  ``APPTReview.appt_entropy_head_saturation_flat,
  ``APPTReview.density_appt_head_spectral_cubic,
  ``APPTReview.density_appt_head_positive_spectrum,
  ``APPTReview.density_appt_paper_head_stability,
  ``APPTReview.paper_head_entire_interval,
  ``APPTReview.paper_head_pivot_positive,
  ``APPTReview.paper_head_conditions,
  ``APPTReview.density_appt_paper_head_conditions,
  ``APPTReview.density_appt_head_conditions_at_pivot,
  ``APPTReview.sorted_entropyHead_conditions_from_budget,
  ``APPTReview.normalized_spectrum_cubic_stability,
  ``APPTReview.trace_normalized_contrast,
  ``APPTReview.nonnegative_lt_of_cube_lt,
  ``APPTReview.entropyHead_deficit_nonneg,
  ``APPTReview.entropyHead_first_square,
  ``APPTReview.entropyHead_large_outlier_deficit,
  ``APPTReview.entropyHead_outlier_bounds,
  ``APPTReview.entropyHead_lt_two,
  ``APPTReview.zero_head_conditions,
  ``APPTReview.zero_head_deficit,
  ``APPTReview.singular_head_conditions,
  ``APPTReview.singular_head_exact_deficit,
  ``APPTReview.missing_star_budget_rejected,
  ``APPTReview.pivot_not_uniform_regression,
  ``APPTReview.trace_normalization_required
  ] "entropy-stability-kernel")

run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.density_appt_head_spectral_cubic "entropy-stability-physical-control"
run_cmd APPTVerification.rejectCorruptTheorem ``APPTReview.entropyHead_outlier_bounds "entropy-stability-scalar-control"
