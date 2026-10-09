# Finite small qutrit–qudit systems, n=3,...,7

The five finite certificates from the interim checkpoint are copied into
the ongoing formalization under their original module names; no immutable
Release source is edited. `SpectrumBound9/12/15/18/21.lean` prove that the
actual ordered eigenvalue list satisfies the corresponding finite PSD
certificate bounds when the two corner matrices are PSD.

`Quantum/SmallMaximum.lean` combines those bounds with the genuine state
semantics, APPT-to-corner-matrix necessity, trace normalization, spectral
purity, and the explicit attaining APPT density states. Its theorem covers
all `3 ≤ n ≤ 7` without additional matrix-PSD hypotheses.

**Important scope:** `n=8` (dimension 24) still requires its finite
certificate and final state-level bridge, and the final all-`n` theorem is
not yet supplied here. The GitHub Actions small-state workflow independently
compiles this module before it can be declared verified.
