# Coupled APPT entropy-order and dimension transition

This ordinary written proof covers the original complex density matrices
that remain PPT under **every global unitary**. Let D=mn,
E_alpha=max_APPT(log D-S_alpha), and G_alpha the exact integer-rank
projection bulk. Let alpha_0 be the unique positive/negative critical
crossing proved in the [fixed-order transition paper](../appt-critical-order-transition-20261015/README.md),
d_0 its critical value, and z_+,z_- its unique critical anomaly parameters.

For each fixed U,A, set alpha=alpha_0+u/m and
a=(n-d_0 m^2)/m, with |u|<=U and |a|<=A. Uniformly over **all** such
integer pairs m<=n and real u, the full actual optimum satisfies

    mD(E_alpha-G_alpha)
       =max{0,alpha_0 z_+(A_++sigma_+u-a),
               alpha_0 z_-(A_-+sigma_-u-a)}+O_(U,A)(1/m).

Here A_s is the explicit individual onset linear coefficient from the
[crossing-envelope paper](../appt-entropy-onset-envelope-20261015/README.md),
and sigma_s=D'_s(alpha_0), with sigma_+>0>sigma_-.
The exact eventual reduction retains integer bulk and the two compact
one-anomaly families, every optimizing matrix/unitary orbit, every
sign/parameter/rank tie, zero omitted mass and exact protection equality.
Every optimizing anomaly has z=z_s+O_(U,A)(1/m). A fixed positive gap
between the three limiting expressions selects every actual optimizer's
family eventually. Limiting ties do not decide finite-dimensional winners.

The minimal **final** bulk onset, defined using every larger integer n
while holding the same alpha fixed, satisfies uniformly for |u|<=U

    N_(alpha_0+u/m)(m)=d_0 m^2
          +max{A_++sigma_+u,A_-+sigma_-u}m+O_U(1).

It also lies between ceil(nu_m^*(u)-C_U m^-3) and
ceil(nu_m^*(u)+C_U m^-3) for the exact compact crossing envelope.
The two integer ceilings can differ. Uniformity is proved with moving
kernels and a relative tail deformation; it is not inferred by inserting
a moving order into a pointwise fixed-order theorem.

![Limiting transition law, with illustrative numerical constants](figures/coupled-transition.png)

The figure illustrates the limiting law, using numerically evaluated
constants: alpha_0 about 0.552520550708, d_0 about 0.177384787663,
and frontier intersection (u_c,a_c) about (4.46632711583,0.921104196826).
These decimals are neither exact definitions nor rigorous interval
certificates. The dashed sign-equality line also extends into the bulk
region, where neither anomaly wins. This is not an exact finite phase
diagram. [SVG](figures/coupled-transition.svg), [provenance](figures/PROVENANCE.json)
and [plot source](figure.py) are included; the mathematical constants are
defined analytically in the proof. The numerical drawing is not evidence
for the full feasible-set theorem.

[Full K0-K3 manuscript](PAPER.md), [target map](THEOREM_MAP.md),
[independent ordinary read](REVIEW.md), [source binding](REVIEW.json),
[final status binding](FINAL_STATUS_BINDING.json), and
[complete retained evidence](../../verification/appt-coupled-order-ordinary-20261015/README.md).
The full 336-line revised mathematical source, original version, actual
domain clarification, disclosed reviewer contribution and all four author/
independent PASS runs are retained. The reviewer independently wrote and
ran a separate control program. No numerical grid is claimed to enumerate
the full quantum feasible set. This internal AI-agent read is not external
human peer review or Lean verification.

Author controls: Python 3 with Sympy 1.9 and Mpmath 1.2.1,
`python3 checks.py`. Each execution retains its own source and results.
Plotting additionally uses NumPy and Matplotlib; it does not enter the
analytic proof. The [bounded literature screen](LITERATURE_SCREEN.md)
records primary-source abstracts/metadata, without an exhaustive priority claim.

This refines the existing APPT line. It adds no major-conjecture count,
arbitrary moving-order theorem, effective cutoff, all-finite-dimensional
classification, universal exact single ceiling, or exact finite transition
count. The C/E/H/I/J inputs and old Lean audit roots remain unchanged.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original material all rights reserved;
third-party attribution/licenses retained. No submission, email, Release or DOI.
