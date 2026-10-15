# Actual independent J control history

The resumed independent review agent's first J run
`j-runs/20261015T065002.850890Z` failed the integral/direct-alpha-derivative
comparison. Its source snapshot and FAIL are retained. A diagnostic-only
error-message expansion was made and the full run was repeated at
`j-runs/20261015T065021.994809Z`; this also failed, now locating the case:
alpha=1, positive sign. Direct `mp.diff` through the piecewise raw quotient
for psi at its removable alpha=1 singularity gave 0.04369590438686...,
whereas the stable integral gave 0.04369593283021....

This was a reviewer numerical-helper defect. The mathematical manuscript
uses an analytic removable singularity and an exact integral, and was not
changed. The control now evaluates the independent exact derivative

    partial_alpha(psi_alpha(y)/alpha)|_(alpha=1)
                              = y*(log y)^2/2-psi_1(y)

at alpha=1; every other tested order still uses direct numerical
differentiation. The actual failures and their source versions are kept;
a later PASS does not erase them. This record is separate from both the
author's control history and the predecessor independent reviewer's run.

The corrected run `20261015T065106.403365Z` passed. A later explicit
ZeroDivisionError check was added for the raw alpha=1 quotient so the third
listed shortcut rejection is directly executed; the complete strengthened
run `20261015T065449.410035Z` also passed. No manuscript change was made.
