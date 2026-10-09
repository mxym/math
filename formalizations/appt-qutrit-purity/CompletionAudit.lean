import APPT.Quantum.Maximum
import APPT.SparsePolynomial
import Verification.ReplaySupport

-- The maximum theorem is deliberately first: the negative kernel control
-- corrupts this exact final theorem, not an unrelated arithmetic lemma.
run_cmd APPTVerification.replayAndCorrupt [
  ``APPT.Quantum.appt_purity_maximum_formula,
  ``APPT.Quantum.appt_purity_maximum,
  ``APPT.Quantum.targetPurity_isGreatest,
  ``APPT.Quantum.appt_purity_upper,
  ``APPT.Quantum.targetPurity_attained,
  ``APPT.Quantum.density_appt_has_sorted_spectrum,
  ``APPT.SparsePolynomial.cubic_control] "completion-replayed"
