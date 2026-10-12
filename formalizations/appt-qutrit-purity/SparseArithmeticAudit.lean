import APPT.SparsePolynomial
import Verification.ReplaySupport

run_cmd APPTVerification.replayAndCorrupt [
  ``APPT.SparsePolynomial.eval_mul,
  ``APPT.SparsePolynomial.eval_monoTimes,
  ``APPT.SparsePolynomial.eval_merge,
  ``APPT.SparsePolynomial.eval_scale,
  ``APPT.SparsePolynomial.eval_trim,
  ``APPT.SparsePolynomial.mon_mulMon,
  ``APPT.SparsePolynomial.cubic_control] "sparse-replayed"
