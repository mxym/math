# Every-dimensional APPT entropy at growing Renyi order

For actual complex density matrices remaining PPT after **every global
unitary**, write E_alpha=max_APPT(log D-S_alpha), D=mn. The complete
ordinary proof establishes a single uniform **absolute-error** formula:

    E_alpha(m,n)=max{log((m+1)/(m-1)),
                         log3-logD/(alpha-1)}+o(1),

as **D->infinity and alpha->infinity**, uniformly over all integers
2<=m<=n and all growth patterns. The smaller dimension may stay fixed,
grow or oscillate; the order may grow faster than D. Actual normalization,
integer projection ranks and the full quantum feasible set remain.
The uniform absolute-error rate is O(D^(-1/2)+log(alpha)/alpha).

There are also explicit finite bounds for **every** 2<=m<=n and alpha>=2.
With a=alpha-1 and T the displayed maximum, the exact inequalities are

    T-[log(2alpha)/a+4/alpha+4/D] <= E_alpha
    <=T+2m/(D-m)+[2log a+log48+2]/a.

The upper proof counts large positive anomalies using the finite physical
sum p_i^2<=8 and keeps the exact mean bound 1-m/D. The two lower states
are the trace-one normalizations of I+2|v><v| and I+2/(m-1)P, both actual
all-unitary APPT, with the latter having physical
integer rank max(1,floor(D/alpha)). Fractional ranks are not substituted
when alpha>D. The [full P0-P2 proof](PAPER.md) gives every estimate.

![Limiting growing-order transition across local dimensions](figures/growing-order-transition.png)

For m->infinity and alpha/logD->c>0, the limit is
max(0,log3-1/c); c=infinity gives log3. The c=0 limit is zero for m->infinity
even for arbitrary positive orders. With m fixed, **D->infinity** and
alpha->infinity, the limit keeps log((m+1)/(m-1)); at finite c it is the
maximum with log3-1/c. These fixed-m curves are shown above.
[Plot source](figure.py) and [provenance](figures/PROVENANCE.json) are
included. The figure illustrates the proved limit, not exact finite extrema.

The first P2 fixed-m sentence omitted the explicit D->infinity condition;
its literal fixed-D, infinite-order case was false. The independent reviewer
identified m=n=2, whose exact infinite-order deficit is log2, not log3.
The corrected statement and target now explicitly keep D->infinity.
That quantifier correction left P0/P1 unchanged; the subsequent epsilon=1/a
strengthening of their upper error was separately read. [Full finding/version history](REVIEW_HISTORY.md)
retains the original source and first diagnostic PASS; that finite PASS
did not detect or certify the incorrect original P2 quantifier.

[Target map](THEOREM_MAP.md), [full independent read](REVIEW.md),
[read/source binding](REVIEW.json), [final status binding](FINAL_STATUS_BINDING.json),
and [retained evidence](../../verification/appt-growing-order-ordinary-20261015/README.md).
These are independent internal AI-agent ordinary reads, not external human
peer review or Lean. Finite actual-state controls support the analytic
proof without numerically certifying the entire feasible-set maximum.
Author controls: Python 3, Mpmath 1.2.1, `python3 checks.py`; every run
keeps its own source/results. Plotting additionally uses NumPy/Matplotlib.

The bounds give explicit absolute error; they do not supply an exact
finite entropy maximum or all equality spectra, sharp next terms, or
relative accuracy when the leading value vanishes. The inherited finite
graph inputs and old formal audit roots remain unchanged. This refines
the existing APPT direction, adding no major-conjecture count. The bounded
[literature screen](LITERATURE_SCREEN.md) is not a priority certificate.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original rights reserved, third-party notices
retained. No new Lean, submission, email, Release or DOI.
