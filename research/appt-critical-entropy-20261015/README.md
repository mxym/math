# Exact critical-window APPT entropy optimizers

For EACH fixed finite entropy order alpha>0, including von Neumann entropy,
and each fixed A, sufficiently large m has an exact formula for the actual
all-global-unitary APPT maximum on the entire |n-d_alpha m^2|<=A m window.
It compares integer q bulk with compact single-positive and single-negative
boundary families, and classifies EVERY optimizing density matrix, retaining
all sign, scalar, integer-rank and bulk ties and all unitary conjugates.

The relative deformation accounts for every omitted anomaly and excludes
arbitrarily tiny tails at finite optimizers. Both negative-diagonal and
negative-edge Schmidt patterns are checked; normalization uses the true
trace and the rank is an actual integer. Alpha=1 is proved separately.

At half order, d_(1/2)=5sqrt(5)-11, the nonempty critical profile is uniquely
negative, and the MINIMAL final bulk onset has the refined expansion

    N_(1/2)(m)=(5sqrt(5)-11)m^2+[(27-11sqrt(5))/2]m+O(1).

Its exact continuous crossing envelope yields a two-ceiling enclosure whose
REAL arguments differ by O(m^-3); the integer ceilings can differ when that
narrow interval contains an integer. No unconditional single-ceiling formula
is asserted. The all-larger-n quantifier is part of the result.

[Complete H0-H5 proof](PAPER.md), [initial target map](THEOREM_MAP.md),
[separately declared half-order follow-up](FOLLOWUP_TARGET.md),
[independent ordinary read](REVIEW.md), [source binding](REVIEW.json),
and [final status-only binding](FINAL_STATUS_BINDING.json).
The complete 681-line reviewed manuscript, C/E/W dependencies, true
source/control histories and resumed reviewer records are preserved in
[the shared evidence directory](../../verification/appt-critical-entropy-ordinary-20261015/README.md).

This is ordinary written mathematics with a separate AI-agent internal
read, not external human peer review or complete Lean. It is eventual in
m with fixed alpha,A; no effective cutoff, all-finite/all-growth theorem,
ASEP bulk assertion, enlarged old audit or new major-conjecture count.
The [general crossing-envelope refinement](../appt-entropy-onset-envelope-20261015/README.md)
and [unique order transition](../appt-critical-order-transition-20261015/README.md)
extend the same APPT line.

Author controls can be reproduced with Python 3, Sympy 1.9 and Mpmath 1.2.1:
`python3 checks.py`. Every execution preserves new result/source files;
old runs are historical versions, not alternate current theorem sources.
These finite computations support the analytic proof and do not enumerate
the quantum feasible set. No Lean/Lake/kernel audit is invoked.

Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original material all rights reserved;
third-party inputs retain their own attribution and licenses. No new
external submission, email, Release or DOI.
