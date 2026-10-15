# Finite APPT entropy bounds and an elementary superlinear formula

For the original complex all-global-unitary APPT density matrices, put
D=mn, a=alpha-1, q=(m+1)/(m-1), t=q-1, and
H=max(logq,log3-logD/a). The [complete R0-R2 proof](PAPER.md) gives,
for EVERY integer 3<=m<=n and EVERY real alpha>=2,

    E_alpha<=H+log27/a+4m/(D-m).

Its O(1/alpha) order-dependent error removes an earlier logarithmic loss,
but its dimension term is larger: it is NOT a pointwise improvement of
the older total error. R2b takes the smaller of both valid finite bounds.
An actual projection of INTEGER rank floor(D/(alpha*t)) proves

    E_alpha>=logq-[log(2alpha*t)+1]/a

when alpha*t>=2 and D/(alpha*t)>=2. The state is (I+tP)/(D+t*k),
with rank(P)=k and full density rank D; the exact trace factor remains.
Together with the actual pole lower bound these imply E_alpha~H whenever
m->infinity, n>=m and alpha/m->infinity, uniformly over all aspect ratios,
including vanishing H and orders larger than D.

The older [calibrated all-order theorem](../appt-growing-renyi/ALL_ORDER_VARIATIONAL.md)
ALREADY proves the full all-positive-order/all-aspect relative range.
This note provides a simpler superlinear maximum formula and an alternative
entropy-only scalar profile on that existing range. It is not a first
closure or an unrestricted-order relative MOMENT theorem with 3 replacing
the exact normalized peak. Exact finite entropy extrema and all equality
spectra, fixed-m relative synthesis and all-aspect spectral rigidity are
not supplied by this note.

The first local scope screen missed the later calibrated companion; the
author corrected that before independent review. The independent reader
then identified the false implication of total pointwise error dominance.
Both findings, the actual original source and first finite author PASS,
and all subsequent versions remain. A finite PASS did not establish novelty.
The requirements pin was also corrected to the actual Mpmath 1.2.1 runtime;
the original pin and reviewed pre-append log remain. No mathematical
control was rerun for these status/runtime metadata changes.

[Target map](THEOREM_MAP.md), [history](RESEARCH_LOG.md),
[full independent read](REVIEW.md), [read/source binding](REVIEW.json),
[final publication-byte binding](FINAL_STATUS_BINDING.json), and
[retained ordinary evidence](../../verification/appt-finite-entropy-ordinary-20261015/README.md).
One author run and a separate independent program actually passed;
all explicit rejected variants are retained. Finite diagnostics do not
certify the original universal quantum optimum. Python3/Mpmath1.2.1,
`python3 checks.py`; original execution bytes remain in control-runs/.
Internal AI-agent ordinary review, no complete Lean or external human
peer review. No new major count, priority certificate, old audit expansion,
submission, email, Release or DOI. Yongxian Zhang, South China University
of Technology; no external funding; OpenAI AI assistants assisted.
Original rights reserved, all third-party notices retained.
