import APPTReview
import Verification.ReplaySupport

#print axioms APPTReview.density_appt_witness_posSemidef
#print axioms APPTReview.diagonal_appt_star_bound
#print axioms APPTReview.entropyCorrection_lower
#print axioms APPTReview.entropyCorrection_head_strict
#print axioms APPTReview.multilevel_sos_nonneg

run_cmd do
  APPTVerification.replayAndCorrupt [
  ``APPTReview.density_appt_witness_posSemidef,
  ``APPTReview.appt_eigenvalue_witness_posSemidef,
  ``APPTReview.diagonal_appt_star_bound,
  ``APPTReview.psd_shifted_star_bound,
  ``APPTReview.multilevel_sos_nonneg,
  ``APPTReview.explicit_purity_gaps,
  ``APPTReview.entropyCorrection_lower,
  ``APPTReview.entropyCorrection_head_strict,
  ``APPTReview.absolutelyPPT_right_iff]
    "verification/kernel/review"
