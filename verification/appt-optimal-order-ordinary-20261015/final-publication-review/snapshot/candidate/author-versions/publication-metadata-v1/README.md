# The optimal entropy order for the final APPT bulk onset

This complete ordinary written proof optimizes the **actual integer final
onset over every positive finite Renyi order**, including von Neumann.
The quantum domain is the original complex density matrices remaining PPT
after **every global unitary**. Let E_alpha=max_APPT(log D-S_alpha) and
G_alpha be the exact integer projection bulk, D=mn. N_alpha(m) is the
least N such that E_alpha(m,n)=G_alpha(m,mn) for **every integer n>=N**;
allow +infinity if no such N exists. The order stays fixed across those n.

For sufficiently large m, the minimum over all alpha>0 is finite and
attained, and

    min_(alpha>0) N_alpha(m)=d_0*m^2+a_c*m+O(1).

EVERY minimizing order satisfies

    alpha=alpha_0+u_c/m+O(m^-2).

For each fixed H>=0 the same O_H(m^-2) location holds for EVERY positive
order whose final onset is at most H above that true integer minimum.
The global minimizing set is nonempty, closed and compact. Integer ties
remain; no unique finite minimizing order is asserted.

The exact constants are defined in the separately reviewed
[critical-order](../appt-critical-order-transition-20261015/README.md) and
[coupled-window](../appt-coupled-order-window-20261015/README.md) papers:

    u_c=(A_--A_+)/(sigma_+-sigma_-),
    a_c=A_++sigma_+u_c=A_-+sigma_-u_c,
    sigma_+>0>sigma_-.

Illustrative decimals are alpha_0 about 0.552520550708,
d_0 about 0.177384787663, u_c about 4.46632711583 and
a_c about 0.921104196826. They are not exact definitions or rigorous
interval certificates. The finite best order has a first correction
u_c/m; the leading crossing alpha_0 alone does not give that correction.

The [L0-L2 proof](PAPER.md) first treats any preassigned compact positive
order interval containing alpha_0. An actual-state lower barrier localizes
all possible minimizers before the uniform coupled formula is applied.
The [new M0-M2 proof](GLOBAL_ORDER.md) then excludes all orders <=1/2
and >=2 at a common actual dimension above the candidate best onset.
For tiny orders it divides each error by alpha before taking uniform
bounds; for large orders it controls a growing logarithmic window, then
uses one fixed state's entropy monotonicity and the all-order bulk bound.
These are separate proofs for the unrestricted optimization, rather than
an automatic extension of a compact-order theorem.

[L target map](THEOREM_MAP.md), [M target map](GLOBAL_TARGET.md),
[L independent read](L_REVIEW.md), [M independent read](M_REVIEW.md),
[L source binding](L_REVIEW.json), [M source binding](M_REVIEW.json),
[final status binding](FINAL_STATUS_BINDING.json), and
[retained evidence](../../verification/appt-optimal-order-ordinary-20261015/README.md).
The ordinary reads are internal AI-agent reviews, not external human peer
review or Lean verification. Reviewer algebraic contributions and source
versions are disclosed. Finite controls support the analytic proof; they
do not numerically enumerate the full quantum feasible set or certify a
global continuous-envelope optimizer.

Author diagnostics use Python 3 and Mpmath 1.2.1:
`python3 checks.py` and `python3 global_checks.py`. Each run preserves its
source/results. The global program selects nine pure scalar definitions
from checks.py by AST and does not import or rerun its diagnostics.

The unrestricted result concerns the minimum FINAL onset and fixed-gap
orders. It supplies no exact finite threshold, effective starting dimension,
unique finite order, or uniform whole-extremum classification for arbitrary
moving orders. It refines the existing APPT direction and adds no major-
conjecture count or new Lean/audit roots. Existing bounded primary-source
screens provide context without an exhaustive historical-priority claim.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original material all rights reserved;
third-party attribution/licenses retained. No submission, email, Release or DOI.
