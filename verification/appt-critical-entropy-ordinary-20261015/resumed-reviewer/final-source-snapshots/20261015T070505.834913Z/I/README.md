# Exact crossing envelopes for every fixed positive entropy order

On the ORIGINAL all-global-unitary APPT set, the minimal FINAL integer bulk
onset N_alpha(m) obeys, for every fixed finite alpha>0 and sufficiently
large m,

    ceil(nu_alpha,m^*-C_alpha m^-3)<=N_alpha(m)
                                <=ceil(nu_alpha,m^*+C_alpha m^-3).

The center is an explicit compact scalar maximum over both boundary signs;
each exact real-rank value is B_alpha(r)-log(1-g_s/D), including von Neumann
entropy by a separate calculation. The proof restores both actual integer
rank errors and uses the full physical critical-window classification and
the all-larger-n theorem. It does not promote fractional ranks to states.

The [complete I0-I3 manuscript](PAPER.md) also computes the linear coefficient
by maximizing over ALL leading critical ties, without assuming uniqueness:

    N_alpha(m)=d_alpha m^2+a_alpha m+o_alpha(m).

Its conditional O(1) improvement assumes nondegenerate critical maxima.
The [separate J0-J3 proof](../appt-critical-order-transition-20261015/README.md)
subsequently proves that condition for every fixed positive alpha, giving
the unconditional O(1) remainder. The exact two-ceiling enclosure still
retains possible integer coincidences. No single exact ceiling is inferred.

[Target map](THEOREM_MAP.md), [independent ordinary read](REVIEW.md),
[read binding](REVIEW.json), [final status binding](FINAL_STATUS_BINDING.json),
and [actual author failure/correction history](CONTROL_HISTORY.md).
The complete 313-line reviewed source and both author/reviewer raw failures
are in [shared evidence](../../verification/appt-critical-entropy-ordinary-20261015/README.md).

This is a full ordinary written proof in the existing APPT line, with
independent internal AI-agent review and no new Lean. Each alpha is fixed
before dimensions. No effective starting dimension, every-finite formula,
varying-alpha uniformity, ASEP bulk result, old audit enlargement, or new
independent major-conjecture count is asserted.

For the author controls use Python 3, Sympy 1.9 and Mpmath 1.2.1, then
`python3 checks.py`. Runs retain their own input versions. The multistart
scalar search is a finite diagnostic, not a global certificate or the
whole feasible-set proof. The first endpoint-omission failure is retained.

Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original material all rights reserved;
third-party inputs retain their notices. No submission, email, Release or DOI.
