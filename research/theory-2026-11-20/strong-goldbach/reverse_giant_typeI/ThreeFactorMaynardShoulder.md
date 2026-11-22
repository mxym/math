# A three-factor reverse shoulder at the common raw cutoff

Use the common-\(V\) double Vaughan identity (1) of
[the complementary short-label proof](../raw_complementary_vaughan/Proof.md),
with \(V=\exp((\log\log N)^3)\), and reopen the genuine long labels
as in [GroupedMaynardShoulder.md](GroupedMaynardShoulder.md).
The prescribed even target, \(x=a f g\), \(y=m c h k=N-x\),
genuine weight \(\mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m)\),
original \(y/m\in I\), roughness and unit restrictions all
remain the same. Take independent dyads on \(a,f,g,m,c,h\).
The free \(k\) has **no further interval gate**.

Write \(u,v,w\) for the exponents of the true \(m,c,h\) dyads
(base \(N\)), \(\beta\) for that of \(f\), and
\(\delta=u+v+w-1/2\). Suppose \(\delta>0\) and all the following
inequalities have fixed positive reserves:
\[
 v+6\delta<w<\frac1{10}-3\delta-\frac35 v,\qquad
 \max\bigl(u+2\delta,\ v+w+\tfrac14+\tfrac{13}2\delta\bigr)
                 <\beta<\tfrac12-3\delta-v .                   \tag{1}
\]
Then the entire signed contribution in this box is
\(O_A(N(\log N)^{-A})\) at every prescribed even target, for
every fixed \(A>0\). The input is
[Maynard, *Primes in arithmetic progressions to large moduli III*,
Proposition 5.2](https://arxiv.org/html/2006.08250v1#S5),
not two-factor Proposition 5.3.

An example of an admissible exponent shape is
\[
  (m,c,h,k)=(.402,.020,.080,.498),\qquad
  (a,f,g)=(.590,.408,.002).
\]
The free \(k\) exponent follows from centrality, not a gate.
Here \(\delta=.002\), \(w=.080<.082\), and
\(.406<\beta=.408<.474\). The raw outer exponents of \(a,mc\)
are .590,.422, with sum 1.012 and reciprocal first exponent
\(.7(1.012)+.25(.590)-.85=.0059>0\); also neither
[asymmetric raw inequality](../raw_complementary_vaughan/RawMobiusBV.md)
holds. The two-factor reverse grouping with first modulus \(m\)
fails because \(7(.402)+12(.100)=4.014>4\). Grouping first
\(mc\) or \(mh\) would require source exponent above .426 or
.486, respectively; available source subsets not using \(a\)
have exponent at most .410, and those using \(a\) exceed the
pertinent upper limit. Any first modulus not containing \(m\)
is too small for the two-factor factorization inequality.
The forward factorized modulus \(a f\) is at exponent .998
and outside the forward rail. These are strict size margins,
not an arithmetic occupancy assertion.

As in GroupedMaynardShoulder, this is additive to the preceding
**raw** deletions only on full independent boxes contained in
the raw complement. One removes those raw gates first, then
reopens the long weights on their complement, at the same
common \(V\). The example has all the requisite margins.
We do not feed an arbitrary curved raw boundary into the
dispersion theorem.

## Proof

Use exactly the true moving-\(y\) cuts, freezing and smoothing
of [ReverseMaynardShoulder.md](ReverseMaynardShoulder.md), §1.
Open only the rough test on \(k\) by a short \(e\mid k\),
and pay the omitted positive tail on the physical divisibility
\(e\mid y\), as there. This time keep the genuine three modulus
coordinates
\[
                    q_1=m,\qquad q_2=c,\qquad q_3=h e .
\]
The \(z\)-rough \(h\) and smooth sieve label \(e\) are uniquely
recovered from \(q_3\). Thus its coefficient is bounded by
\(L=\log N\), with no subpower number of redundant terms in
the errors. The \(q_1\)-coefficient is \(Q_T(m)\), bounded by
\(\tau(m)\), and the \(q_2\)-coefficient is the literal
\(\mu(c)\). All \(q_i\) are units at \(N\), but may share primes
with one another. Their product is the actual divisor of \(y\).

The source is \(f\) with its actual rough unit-masked
\(\Lambda(f)\) and \(a g\) with its divisor coefficient.
The real smooth test is separated by Mellin, and the
genuine \(f\)-coefficient satisfies exact auxiliary-unit
Siegel--Walfisz at its polynomial scale, also under the
log-bounded real twists. These facts were verified in the
reverse two-factor proof and depend on neither which
moduli are summed nor their factor count.

In Maynard's Proposition 5.2 take lengths \(Q_1,Q_2,Q_3\)
at exponents \(u,v,w+o(1)\), the SW length \(F\) at \(\beta\),
and \(Q_1Q_2Q_3=N^{1/2+\delta'}\) with
\(\delta'=\delta+o(1)\).
Since (1) has reserves, the precise displayed inequalities of
that proposition hold with a sufficiently small fixed
analytic epsilon; its extra \(5\epsilon\) losses and \(o(1)\)
from \(e\) fit the margins. Its arbitrary reduced residue
supremum includes the true class \(N\bmod q_1q_2q_3\).
Use it at that class throughout. Normalize the source by
at most a power of \(L\) to meet its divisor coefficient
hypothesis, as in the two-factor proof.

The weighted modulus error lifts by exactly the
true-residue crossed-moment argument, now with at most
\(\tau_3(|N-x|)\) ordered modulus triples dividing \(N-x\)
at each actual source product \(x\ll N\).
The omitted \(x=N\) is excluded by the source unit mask.
The model harmonic is
\(\sum_{q\ll N}\tau(q)^C\tau_3(q)/\varphi(q)\ll L^{O_C(1)}\).
Cauchy using the absolute discrepancy as measure then absorbs
all divisor weights from the arbitrary-log unweighted estimate.
No weighted estimate is asserted at a supremum of
different residues in this lifting step.

At the exact principal \(1/\varphi(m c h e)\), fix \(x,m,h,e\).
The \(c\)-sum has the actual interval, \(c>V\), \(c\) rough
and \((c,N x)=1\); all remaining gates and the frozen score
are independent of \(c\). Use the signed rough harmonic
\(\mu(c)/\varphi(Hc)\) for \(H=m h e\), with the same local
ratio as in ReverseMaynardShoulder.
At the common smaller \(V\), take the Rankin line
\(\sigma=1-\log\log L/(2(\log L)^2)\) of the complementary
short-label proof. The unexcluded \(1+O(1/p)\) modification
in this Euler ratio contributes a bounded absolute product
on that line. The marked exclusions and the Mertens/Rankin
tails therefore give arbitrary-log saving
\(O_A(L^{-A}/\varphi(H))\).
Sum the remaining factors with true reciprocal weights,
using \(\varphi(m h e)\ge\varphi(m)\varphi(h)\varphi(e)\),
and the physical source by its ordinary divisor moment.
The principal vanishes as claimed.

This is signed cancellation in the genuine three-factor
boxes (1), not a sign for the remaining raw complement or
a binary Goldbach implication.
