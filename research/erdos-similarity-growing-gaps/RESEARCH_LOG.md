# Core problem and remaining bottleneck

## Problem selection

The target is the Erdős similarity conjecture, formulated in 1974: every
infinite subset of the line is affine non-universal for positive-measure
sets. The exact-geometric case has a public 2026 proof. The research here
addresses the next obstruction, sequences with unbounded logarithmic gaps,
rather than modifying a constant in the geometric statement.

Other screened core targets were the intersecting rank-six Ryser case and
the four-cell balanced Gaussian first-Hermite problem. Ryser's low-degree
subcases already follow from the published degree inequality; proving them
again would not answer the rank-six problem. In the Gaussian problem,
equal covariance energy does not remove the optimized cell prices.
Those status distinctions prevented a premature conjecture-resolution claim.

## Completed extension

The former schedule fixes branching, depth and gap before sending the
starting position to infinity. It cannot directly be substituted into a
sequence whose largest useful logarithmic gap grows with that position.
The new proof explicitly allows all those tree parameters to change. The
full tree is bounded uniformly by

\[
 T_d\le(2b)^d(L+2g),
\]

and the choice $b=O_p(D)$ and $d=\exp(O_p(D))$ leads to
$\log T_d=o(\log U)$ when $D=o(\log\log U)$. Sampling is restricted to
the same annulus on which this $D$ is valid. This closes a genuine
quantifier gap: moving to another larger $U$ while retaining the old
gap bound is not allowed. Exceptional centers can still be repaired by
the rest of the infinite tail, without controlling its later gaps.

Theorem 2 includes infinitely many zero-logarithmic-density examples
with adjacent ratios tending to zero, and block sequences with enormous
interblock gaps. The finite routing architecture itself is inherited;
the variable schedule and usable sequence classes are the added work.

## Why the quadratic-logarithm case is still outside the proof

For $a_n=2^{-n^2}$, logarithms in $[U/R,RU]$ have gaps comparable to
$\sqrt U$. In the actual schedule (19), $b\ge24D/p$ and
$d\ge2^{b-1}\log(2/p)$, while even $T_d\ge b^dL$.
If $D$ is comparable to $\sqrt U$, these lower bounds imply
$\log T_d\gg\log U$. The required guard $T_d\le U$ is therefore
impossible in this schedule. This is an analytic obstruction to the
particular construction, not a disproof of the conjecture or of all
routing methods. The doubly exponential sequence is sparser still.

The exponential depth comes from waiting along a center route for a
default event of probability $2^{1-b}$, while the continuum miss bound
requires branching of order $D/p$. Passing to a more distant scale does
not resolve that conflict for quadratic logarithms. A further attack
must change how center coverage is obtained or how continuum complexity
is paid for; an extra constant adjustment cannot close it.

This package publishes the completed growing-gap class. It does not
rename the remaining quadratic or arbitrary-sequence problem as solved.
