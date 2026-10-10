import APPTReview
import Verification.ReplaySupport

run_cmd APPTVerification.replayAndCorrupt [
  ``APPTReview.appt_eigenvalue_witness_posSemidef,
  ``APPTReview.diagonal_appt_star_bound,
  ``APPTReview.psd_shifted_star_bound,
  ``APPTReview.absolutelyPPT_right_iff,
  ``APPTReview.multilevel_sos_nonneg,
  ``APPTReview.entropy_quartic_positive,
  ``APPTReview.explicit_purity_gaps] "review-kernel"
