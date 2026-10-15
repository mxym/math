# Actual optimizing spectra in the linear-order APPT peak--bulk window

For original complex density matrices remaining PPT after EVERY global
unitary, take m->infinity, n>=m, alpha/m->c in (0,infinity), and
3^alpha/(mn)->r in [0,infinity). This allows exponentially large aspect
ratios. The [complete proof](PAPER.md) gives necessary AND sufficient
conditions for relative entropy-deficit optimality over the entire actual
APPT set, using three explicit spectral quantities:

- Distance of the actual width/mixing pair to the FULL compact maximizing
  set of the credited scalar F_*(c,r) tends to zero, retaining all ties.
- The actual middle eigenvalues saturate their two-endpoint chord,
  equivalently the explicit spectral spread J tends to zero.
- The actual normalized peak moment saturates its physical cap, P->0.

The proof keeps N=D-m^2+2 middle slots, exact trace normalization, every
exceptional moment and the width-two boundary. The scalar value theorem
was already complete in the older linear/all-order manuscripts; this is
a new spectral classification in the stated window, not another value
theorem or a complete classification at every order/aspect.

When r=0 the condition reduces to the empirical law of m(D*lambda-1):

    (1-h_c)delta_(-2h_c)+h_c delta_(2(1-h_c)),
    h_c=1/(2c)-1/(exp(2c)-1).

Physical bounds on the exceptional powers justify the weak-convergence
converse. They are not inferred from weak convergence alone. Both an
actual projection-only sequence with D*lambda_max->1 and an actual
protected-spike sequence with D*lambda_max->3 can attain this same
near-optimal body law. Thus it does not imply a unique extreme-eigenvalue
pattern or operator flatness.

If r>0 and a maximizing width/mixing cluster is (l,h) with l<2, then
m(3-D*lambda_max)->3lh+2l^2/(2-l), and every other normalized eigenvalue
tends uniformly to one. At l=2 only the disappearing peak-moment conclusion
is asserted; the interior formula is not extended through its singularity.
All maximizing scalar pairs, including zero-width redundant mixing
parameters and every tie, have actual integer-rank APPT realizations.

[Target map](THEOREM_MAP.md), [author record](RESEARCH_LOG.md),
[full independent read](REVIEW.md), [source/execution binding](REVIEW.json),
[final publication-byte binding](FINAL_STATUS_BINDING.json), and
[ordinary evidence](../../verification/appt-linear-rigidity-ordinary-20261015/README.md).
The author program and a separately written independent program actually
ran; their finite exact controls support the analytic proof without
certifying all physical matrices or limits by sampling. Python3 with
Mpmath1.2.1, `python3 checks.py`; original run bytes remain.

Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Independent internal AI-agent ordinary
review, no external human peer review, complete Lean, old audit expansion,
general APPT=ASEP result, new major count, priority certificate, submission,
email, Release or DOI. Original rights reserved, third-party notices kept.
