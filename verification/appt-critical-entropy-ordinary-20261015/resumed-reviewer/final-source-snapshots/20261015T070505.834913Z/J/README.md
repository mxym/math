# Unique critical anomalies and one entropy-order transition

For EVERY fixed finite alpha>0, each full positive/negative APPT critical
ratio has exactly one maximizer, with strictly negative curvature. These
anomalies and their optimal values D_+(alpha),D_-(alpha) are real analytic.
D_+ has strictly positive derivative and D_- strictly negative derivative.
There is exactly one transverse crossing alpha_x in (1/2,1).

The actual leading onset d_alpha=max(D_+,D_-) therefore has its unique
global minimum at alpha_x. In the full finite linear critical window,
nonbulk actual optimizers are eventually negative below alpha_x and
positive above it. Both leading signs remain included at the exact
crossing; this does not assert that both win at each finite dimension.

These curvature facts remove the earlier conditional hypothesis and prove
for every fixed finite alpha>0

    N_alpha(m)=d_alpha m^2+a_alpha m+O_alpha(1),

with the explicit all-critical-tie a_alpha from the
[crossing-envelope paper](../appt-entropy-onset-envelope-20261015/README.md).
N retains its original minimal FINAL/all-larger-n meaning. No unconditional
single-ceiling formula, effective dimension cutoff, or varying-order
uniformity is asserted.

[Full J0-J3 proof](PAPER.md), [target map](THEOREM_MAP.md),
[independent full ordinary read](REVIEW.md), [read binding](REVIEW.json),
and [final status binding](FINAL_STATUS_BINDING.json).
The [shared evidence](../../verification/appt-critical-entropy-ordinary-20261015/README.md)
retains the full 230-line reviewed source, independent derivative controls,
both genuine reviewer numeric-helper failures and subsequent PASS runs.
These are internal AI-agent reads, not external human peer review or Lean.

The author diagnostic locates alpha_x near 0.552520550708 and the minimum
d near 0.177384787663. These decimals are numerical illustrations, not
an exact definition or a rigorous interval certificate. The analytic
proof defines the unique crossing without relying on those decimals.
Reproduce author controls with Python 3, Sympy 1.9, Mpmath 1.2.1 and
`python3 checks.py`; each execution keeps its own input versions/results.

This is a refinement of the existing APPT line, not an additional major
conjecture solution, a new Lean theorem, or an enlarged old audit.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original material all rights reserved;
third-party attribution/licenses retained. No submission, email, Release or DOI.
