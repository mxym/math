import APPTReview
import Regression
import Verification.ReplaySupport

run_cmd APPTVerification.replayAndCorrupt [
  ``APPTReview.density_appt_paper_entropyHead,
  ``APPTReview.density_appt_entropyHead_at_pivot,
  ``APPTReview.density_appt_singular_spectrum,
  ``APPTReview.appt_sorted_rankTwo_determinant,
  ``APPTReview.appt_largest_eigenvalue_bound,
  ``APPTReview.appt_sorted_shifted_star,
  ``APPTReview.appt_eigenvalue_witness_posSemidef,
  ``APPTReview.appt_eigenvalue_star_bound,
  ``APPTReview.diagonal_appt_star_bound,
  ``APPTReview.psd_shifted_star_bound,
  ``APPTReview.absolutelyPPT_right_iff,
  ``APPTReview.multilevel_sos_nonneg,
  ``APPTReview.entropy_quartic_positive,
  ``APPTReview.explicit_purity_gaps,
  ``APPTReview.entropy_negative_bound,
  ``APPTReview.entropy_positive_gap_bound,
  ``APPTReview.entropy_head_outlier_margin,
  ``APPTReview.entropyHead_le_two,
  ``APPTReview.appt_eigenvalue_entropyHead_bound,
  ``APPTReviewRegression.productState_density,
  ``APPTReviewRegression.productState_ppt,
  ``APPTReviewRegression.productState_not_appt] "review-kernel"
