import APPT.Finite24Sparse.Leaf002
import APPT.Finite24Sparse.det04Term1Product
import Verification.ReplaySupport

run_cmd APPTVerification.replayAndCorrupt [
  ``APPT.Finite24.eval_det04Term1Coeffs,
  ``APPT.Finite24.block002_nonneg,
  ``APPT.SparsePolynomial.eval_decodeCubic] "merge-barrier-replayed"
