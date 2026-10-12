# Candidate improvement of the mixed Bellman ceiling

**Research note, 7 October 2026.  NOT YET A THEOREM.**

This note records a strictly stronger candidate mixed Bellman potential found
after the certified \(e^{1.049}<2.855\) theorem.  It is intentionally marked
as incomplete until the imbalanced-tail certificate is regenerated and
independently replayed.

For the entry-005 product/join class use
\[
D=d+1,\qquad H=1/a(K),\qquad Q=\frac{a(K)R(K)}{g(d)}.
\]
The candidate potential is
\[
\boxed{
\log Q(K)\le
\alpha\left(D-\frac{H^2}{D}\right)
+\beta\left(D-\frac{H^4}{D^3}\right)}
\]
with the exact rational coefficients
\[
\boxed{\alpha=\frac{271}{6250}=0.04336,\qquad
\beta=\frac{5453}{10^6}=0.005453,}
\]
and hence
\[
T=\alpha+\beta=\frac{48813}{10^6}=0.048813.
\]
If the remaining tail certification closes, spectral reduction gives
\[
\Gamma_{\mathcal C}\le e^{1+T}
=e^{1.048813}\approx2.85426110.
\]

## Why these coefficients

Within the quadratic/quartic family, a cutting-plane search shows that the
limiting coefficient frontier is governed by two mechanisms:

1. the \(5\times5\) finite product state; and
2. the balanced large-dimension asymptotic state.

Solving the limiting three equations (finite equality, finite stationarity,
balanced-asymptotic equality) numerically to high precision gives
\[
\alpha_\star\approx0.04302948603489656070646,
\]
\[
\beta_\star\approx0.00570676295059625068160,
\]
\[
T_\star\approx0.04873624898549281138806,
\]
with the corresponding formal ceiling
\[
e^{1+T_\star}\approx2.8540420395322595.
\]
That near-frontier choice makes the old large-dimension relaxation extremely
inefficient, so the rational point above deliberately moves toward larger
quadratic weight.  It sacrifices about \(2.2\times10^{-4}\) in the final
ceiling but restores a practical all-dimension certificate architecture.

## Completed checks for the rational candidate

The following items were completed before this note was recorded.

### Finite dimensions

All \(19{,}900\) complete state rectangles
\[
1\le r\le s\le199,\qquad
(H_1,H_2)\in[2,r+1]\times[2,s+1]
\]
were regenerated at the new coefficients and checked by the exact rational
supporting-plane verifier inherited from the certified mixed theorem.

Every rectangle had a strictly negative rational upper bound.  The worst
rectangle was exactly
\[
(r,s)=(5,5),\qquad H_1=H_2=6,
\]
with support term zero and exact upper margin approximately
\[
-1.1187\times10^{-5}.
\]
Thus the entire finite rectangle region is rigorously closed.

### Large-large analytic condition

The existing proof which discards the favorable quartic term reduces the
large-large region to
\[
\frac{2/3+1/m}{\pi}
<
2\alpha e^{1-2T},
\qquad m=\min(r,s).
\]
At \(m=200\), the rational candidate has numerical discovery margins
\[
\frac{2/3+1/200}{\pi}\approx0.2137981402201,
\]
\[
2\alpha e^{1-2T}\approx0.2138037498925,
\]
leaving about \(5.6\times10^{-6}\).
This comparison still needs to be packaged with the same rational
Machin/Taylor proof used by the certified predecessor before it is promoted
to theorem status.

### Imbalanced tail

The tail region is
\[
1\le r<200,\qquad s\ge200.
\]
Regeneration with the exact interval tail engine showed no mathematical
failure.  Before the execution workspace changed, exact-certified cells had
already been generated through substantial portions of this region; for
example the early ranges required only modest dyadic depth.  However, the
complete regenerated certificate was not durably saved.

Therefore the imbalanced tail is the **only substantive certification task
still open** for this candidate.

## Stronger near-frontier candidate

For reference, the still stronger rational pair
\[
\alpha=\frac{4303}{100000},\qquad
\beta=\frac{5707}{10^6},
\qquad T=\frac{48737}{10^6}
\]
passed all \(19{,}900\) finite rectangles after tangent-point regeneration,
with worst exact margin at \(5\times5\) approximately
\(-6.33\times10^{-6}\).  It would give
\[
e^{1.048737}\approx2.85407272.
\]
Its balanced-asymptotic margin is much smaller, causing the simple
large-dimension proof to require a very large cutoff.  It is retained as a
future target rather than the current certification candidate.

## Status

Do **not** cite \(2.85426110\) as a proved upper bound yet.

The currently certified public theorem remains
\[
\Gamma_{\mathcal C}\le e^{1.049}<2.855.
\]

To promote the present candidate, complete exactly these tasks:

1. regenerate and exact-replay the full imbalanced-tail certificate for
   \(1\le r<200,\ s\ge200\);
2. package the \(m=200\) large-large comparison with rational
   \(\pi\)/exponential bounds;
3. replay finite, tail, and large-large checks from a clean checkout;
4. only then update the theorem statement.

The coefficient search and all numerical optimization in this note are
discovery tools.  The eventual theorem must depend only on exact arithmetic,
rational intervals, and the written analytic reductions.
