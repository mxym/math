# Two-bank transport on the true prime-cofactor exterior

Use [the fixed-gap polynomial native score](PolynomialNative.md),
at a prescribed even \(N\) with \(\operatorname{rad}(N)\le L^{B_0}\)
for fixed \(B_0\). Fix \(0<\xi<\gamma=1/2-\epsilon\), and restrict to
its actual \(m\ge N^\xi\) rows with **both \(A,C\) genuine primes**.
In particular their two native coefficients equal 1, but the weights
on \(f,h\) are still \(\log f,\log h\), not weights on all four primes.
All original prime and cofactor lower cutoffs, units, \(y/m\in I\),
and the literal \(Q_y(m)\) remain.

Fix \(\delta>0\). Work on any disjoint union of the product boxes of
ordinary fixed-ratio dyads in the five variables \(A,f,m,C,h\),
permitting independent subinterval cuts in each coordinate. Require
that in each box one can leave one of \(A,f\) and one of \(m,C,h\)
free so that the product of the three other **upper scales** is at most
\(N^{1-\delta}\). This specifies the exterior without a joint sharp
inequality inside a box. The number of boxes is at most \(O(L^5)\).

For every fixed \(D>0\), choose two admissible disjoint \(K\)-color
banks \(B_1,B_2\) as below, with \(K\ge2\) sufficiently large and
fixed. Impose on the original **same actual \(m\)** the two conditions
\[
 m \text{ hits every color of }B_1,\qquad
 m \text{ avoids every prime of }B_2 .                             \tag{1}
\]
**Theorem.** The indicated portion of the original signed native
score is \(O_D(NL^{-D})\). It is disjoint from both native bank covers
in [PolynomialNativeCovered.md](PolynomialNativeCovered.md) and
[PolynomialNativeReverseCover.md](PolynomialNativeReverseCover.md):
a prime \(A\) or \(C\) cannot itself furnish the \(K\) colors. This
does not bound the rows lacking (1), the non-exterior boxes, or the
subpolynomial-\(m\) range.

For instance the scales \(A,f,m,C,h=N^{.60},N^{.40},N^{.20},N^{.15},
N^{.65}\), respectively, are in the exterior (\(f m C=N^{.75}\)),
admit the fixed-gap calibration at \(\gamma=.24\) and small fixed
positive cutoffs, and are not in the prime-inverse theorem's
\((f,mh)\) range. This is a statement about their score, not their
number of rows.

## 1. Two normalized models and their exact character means

Choose the bank exponent grids
\[
 \theta_{1,\nu}=.1+\frac{\nu-\tfrac12}{20K},\qquad
 \theta_{2,\nu}=.15+\frac{\nu-\tfrac12}{20K},\qquad 1\le\nu\le K .
\]
For each exponent use primes in
\([\exp(L^\theta),\exp(2L^\theta)]\), using for example the primes \(1\bmod 4\), with reciprocal
masses in the admissible range of the
[one-prime comparison](../small_radical_reflected_chowla/Proof.md).
They have the required within-family separation \(1/(20K)\).
Take \(Z_1=\exp(L^{.15})\), \(Z_2=\exp(L^{.21})\).
The primes and tag products of \(B_1\) are smaller than \(Z_1/10\);
those of \(B_2\) are smaller than \(Z_2/10\); every \(B_2\) prime
exceeds \(Z_1\) for sufficiently large \(N\).
Both bank minima exceed \(T_y\asymp S\).
All arc and target prime divisors in the proof are below \(z\)
and hence below \(Z_1\), since their radicals are polylogarithmic.

Write
\[
 R_i(n)=1_{P^-(n)>Z_i}\prod_{p\le Z_i}(1-1/p)^{-1}.
\]
Define \(P_2(n)\) to be supported on integers with exactly one prime
from each color of \(B_2\), each to exponent exactly 1, and with no
other \(B_2\)-prime divisor. On this set let
\[
 P_2(n)=\left(\prod_{p\in B_2}(1-1/p)\prod_{\nu=1}^K V_\nu\right)^{-1},
 \qquad V_\nu=\sum_{p\in B_{2,\nu}}\frac1p .
\]
Indeed the CRT density of a selected product \(w\) is
\(\prod_{p\in B_2}(1-1/p)/w\), since a selected prime has
local probability \((1-1/p)/p\), not \(1/p\).
Summing the one-per-color choices gives the stated normalization.
It is \(O_K(1)\). The additional model \(R_1(n)P_2(n)\)
has mean 1, as its two prime alphabets are disjoint.

Let \(\Lambda^*(n)=(\log n)1_{n\ {\rm prime}}\).
Each of \(R_1,R_2,R_1P_2\) can replace \(\Lambda^*\) in
a full projected character slot: for any fixed polynomial
length dyad scale \(X\) and any character modulo \(N b\),
\(b\le L^F\) with \(F\) fixed, their differences from
\(\Lambda^*\) have all prefix sums \(O_E(XL^{-E})\)
for every fixed \(E>0\). For weighted primes this follows
from the zero-free strip used in
[the small-radical major proof, §1](../small_radical_projection/Proof.md),
using \(-L'/L\) in the same truncated Perron argument.
For a nonprincipal inducing character, Iwaniec's strip
and the exclusion of a real zero by the polylogarithmic
primitive real conductor give \(\theta\log X\gg L^c\)
for some fixed \(c>0\) at any fixed log-power height.
The local logarithmic derivative is log-power bounded in
the smaller strip by the same disc comparison. Shift
Perron to \(1-\theta/2\) with height \(L^J\), with \(J\)
chosen for the desired log precision; truncation costs
\(O(XL^{O(1)}/L^J)\) at half-integer endpoints.
For the principal use the ordinary prime number theorem.
Removing proper powers costs \(X^{1/2+o(1)}\) and the omitted
primes of an imprimitive modulus are polylogarithmic.

For the integer models, open all required avoidance by
the positive-error factorial Bonferroni truncations as
in [PolynomialNativeCovered.md, §1](PolynomialNativeCovered.md).
In the planted model first open \(n=w a\), exactly one tag
per color, with \(a\) avoiding all of \(B_2\) as well as
the \(R_1\) exclusions. Each tag and every sieve product is
subpower; the number of assignments is subpower as well.
The prime unit exclusions of the character are already
mandatory and may be omitted from the avoidance alphabet.
The free variable always has polynomial scale \(X/(w e)\).
For nonprincipal inducing characters use Iwaniec Lemma 6
and full periods in the short-conductor case, as in that
proof. The principal is exactly the genuine real-density
calculation above. Both errors are uniform in all real
prefixes: the reciprocal sieve tails are factorially
small, and the subpower floor count has a power reserve.
Sum the tags only by \(\sum_w 1/w=\prod_\nu V_\nu\).
Real partial summation permits fixed smooth masks and
\(1/\log n\) on a polynomial dyad. In particular an
unweighted prime is replaced by \(R_i(n)/\log n\),
or \(R_1(n)P_2(n)/\log n\), not by \(R_i(n)\).

## 2. Transport on the actual score by two projections

Use the real \(y\)-mesh of
[PolynomialNativeCovered.md, §2](PolynomialNativeCovered.md).
The literal \(m\)-endpoints in \(y/m\in I\) and the cutoff
\(T_y\) in \(Q_y(m)\) are frozen on each cell with arbitrary
log accuracy. This applies before or after the model changes:
the changed \(m\) and score-divisor labels divide the same
actual \(y\), and all weighted appearances have a fixed
crossed-divisor envelope times log powers. When smoothing
any independent factor cutoff, the collar consists of
actual divisors of \(x\) or \(y\) in a relative \(L^{-G}\)
interval at a polynomial scale \(X\). The positive count
is \(O(N(L^{-G}+1/X))\), using actual multiples, followed by
the fixed crossed divisor moments. This applies also to
the frozen \(m\)-interval in each cell. Choose its \(G\)
after the first mesh exponent and before \(K\). Thus its
cutoff on the **product** \(m=w_1 m'\) during the first
projection separates by one Mellin integral, with fixed
log-power norm; its phase on \(w_1\) is a product of
bounded entering-label multipliers. In the second
projection use the same separation on \(A=w_2 a\),
including the smooth \(1/\log A\) and the \(A\)-axis mask.
No per-color mesh is used. The two separations do not
alter the actual m conditions (1).

**First projection, using \(B_1\) on the original \(m\).**
Extract one real prime per color \(w_1\mid m\), with the
exact reciprocal hit allocation after excluding bank-square
incidences on \(y\). Put \(m=w_1 m'\); \(Q_T(m)=Q_T(m')\)
since the selected primes exceed \(T\). The prescribed
avoidance of \(B_2\) is unchanged by this division.
Restore square rows after opening with no hidden tag-gcd
mask in the residual: all additional rows still satisfy
\(w_1\mid m\mid y\) and \(p^2\mid y\) for a bank prime,
and their opened score is divisor-bounded. Their total is
arbitrarily log-small by actual multiples and crossed moments.
Thus the true residual on \(w_1\asymp Y\) is one
divisor-bounded coefficient of \(n=m' C h\), including
the true \(C,h\)-prime conditions and \(Q_T\), with squared
norm \(O((N/Y)L^{O(1)})\).

In the source \(x=A f\), apply the full projected
comparison to the centered \(A\)-coefficient from §1
with model \(R_1(A)P_2(A)/\log A\); the other slot is
the actual log-prime \(f\).
Then apply it to the centered \(f\)-coefficient with
model \(R_1(f)\), now with the planted \(A\)-model retained.
In the first case the genuine prime \(f\) ensures
primitive endpoints; in the second the other factor
is \(Z_1\)-rough, so the same endpoint gcd argument
works since \(Z_1>5Y\) for all \(B_1\)-tag shells.
Both actual source factors avoid the entire chosen
bank in each comparison. Their product boxes are
kept strictly inside \((0,N)\), and they are units.
In the full major the centered factor has §1's
character cancellation and the other has the
restricted Bessel bound. Bounded Mellin tag multipliers
are permitted by
[Jiang–Lau–Lü v2, Lemma 6.11](https://arxiv.org/html/2611.12467v2).
Apply the squared comparison and Cauchy with the
actual residual. This replaces the original two weights
by the stated two models to arbitrary-log accuracy.
Now sum back the first-bank tag allocations on those
modeled physical rows. They again give the exact
first hit indicator on the same \(m\); the only
possible discrepancies are the already priced
square rows, with the same divisor envelope even
after these two replacements. Thus neither \(m\)
nor either opposite prime has changed.

**Second projection, using the planted \(B_2\) on \(A\).**
Unpack its unique literal selected product \(w_2\mid A\),
so \(A=w_2 a\) with \(a\) avoiding all \(B_2\).
There is no presumption that the original genuine
\(A\) had these divisors. The new source is \(y=(m C)h\).
In the first replacement here keep the true prime \(h\)
and center \(C\) against \(R_2(C)/\log C\) inside the
grouped \(mC\) factor. At each fixed actual \(m\) its
character estimate is §1, and the physical coefficient
\(Q_T(m)\) is unchanged. For the part modulo \(d_0\)
of a small arc denominator coprime to \(N\), the residue
of \(mC\) first divides by \((m,d_0)\); either it is
impossible or it imposes a class on \(C\) modulo
\(d_0/(m,d_0)\). The class must be reduced since both the
actual and modeled \(C\) avoid all primes of \(d_0\).
Thus the exact reduced-class twist has conductor dividing
\(N\) times a polylogarithmic factor; no assumption that
\(m\) is a unit at \(d_0\) is used. The target-ring
factors treat \(m\) as its actual target-unit value.
Sum the resulting estimates at fixed \(m\) by
\(\sum_m\tau(m)/m\ll L^2\), not by the number of \(m\)'s.
This leaves the true \(m\)-bank conditions, and the
other source slot is still a genuine prime.

Finally center \(h\) against \(R_2(h)\), retaining the
modeled \(mC\) factor. This time the centered \(h\)-slot
is itself \(Z_2\)-rough (both the true and modeled terms);
thus primitive endpoints are valid in both replacements,
even if \(m\) has small factors. In all cases \(m\)
avoids \(B_2\) by (1) and \(C,h\) avoid it on the true
or modeled support, so the chosen bank avoidance is
literal on the entire source. The grouped coefficient
is clipped at fixed \(\tau(mC)\le L^M\) at arbitrary-log
cost using actual \(mC\mid y\) and the fixed divisor
moments, and the equally small removed term in the
linear estimate is bounded by ordinary divisor moments.
The residual has factorizations \(n=a f\), retains
the left model weights, and has squared norm
\(O((N/Y)L^{O(1)})\). In particular the \(1/\log A\)
and \(A\)-mask are separated by the one Mellin
dimension already noted. No mask involving \(w_2\)
is left in the residual. Apply the same major/minor
and residual Cauchy argument. This changes only \(C,h\)
to \(R_2(C)/\log C,R_2(h)\).

All prime replacements are at polynomial source scales
since \(A,f,C,h,m\) each have a fixed positive exponent
on this theorem's support. The mesh, packet count, squared
norm losses, clips and Mellin norms have fixed log exponents
before selecting \(K\); the tight \(B_2\) plant normalization
costs only a constant depending on \(K\).
The rank of the divisor envelopes is fixed independently
of \(K\), since selected tuples are indexed by their
distinct divisor products, or have weights summing to
one. There are \(O_K(1+L^{.2})\) fixed-ratio tag shells.
Choosing the precision first and then \(K\) makes
all four comparison errors arbitrary-log small.

## 3. The final signed integer model

At this stage the same literal equation \(A f+m C h=N\)
has only free integer model factors, with the normalizers,
\(1/\log A,\ 1/\log C\), and exactly the original \(Q_T(m)\)
and conditions (1). Use the selected free coordinate on
each side. Open all model conditions on the free
coordinates by subpower roughness labels and positive-tail
factorial truncations, keeping exact target units separately.
If \(A\) is free, first remove its actual planted \(w_2\);
if \(A\) is fixed, simply retain its model weight.
At any fixed labels the two free integers satisfy one
linear equation in the actual outer coefficients
\(D_x,D_y\), including every chosen short factor.
The central variable has density
\(\varphi(N)/(N D_xD_y)\) when the two coefficients are
coprime and target units, and otherwise has no contribution
on the retained unit support. This is exact ordinary CRT
on \(x\) with at most \(\tau(N)\) unit floor.
The three outer upper scales multiply to at most
\(N^{1-\delta}\); the products and number of short labels
are subpower. Thus all floors, including positive
Bonferroni remainders, total \(N^{1-\delta+o(1)}\).
The main remainders are bounded by the positive
factorial reciprocal tails times fixed log powers.
Open a union of exclusion alphabets on each free
variable only once; across the two sides, actual
compatibility and products, not lcms, are used.

If \(m\) is a fixed outer coordinate in this count,
apply its signed harmonic **in the real model**
before the other outer sums. At fixed \(x\) and the
remaining coordinates and labels, \((m,H)=1\) is the
only compatibility mask involving \(m\), with
polynomial-sized \(H\), because other factors on the
same side may share primes with it. The signed sum is
\(Q_T(m)/m\) on an actual polynomial-scale real
interval, with (1) and smooth log-bounded weights
(including the retained \(1/\log C\) if \(C\) is free).
Open \(Q_T(m)\) with \(d<T\). The labels with primes from
the banks cannot meet \(d\). The hit conditions in
\(B_1\) are a finite expansion into avoidance patterns,
and these together with \(B_2\) avoidance use the
same subpower factorial truncation, now on \(m/d\).
At fixed such labels the free \(m\)-scale is still
polynomial after their removal; exact unit counts
with individual \(\tau(H)\) floors have a power reserve.
The real main is independent of \(d\) apart from \(1/d\),
and requires \((d,H)=1\). The uniform short
\(\sum_{d<T,(d,H)=1}\mu(d)/d=O_E(L^{-E})\)
from [PolynomialNative.md, (3)](PolynomialNative.md)
kills that main. All external absolute reciprocal costs
are fixed log powers.

If \(m\) is the free coordinate, instead open \(d<T\)
in \(Q_T(m)\) along with (1) *before* counting the
two-coordinate lattice. The hit/avoid bank products are
again disjoint from \(d\); their supported variables are
true factors of \(m\), so the label truncation and floors
have exactly the reserve above. At a fixed real point
in the model, the only \(d\)-dependence is its factor
\(1/d\) and \((d,H)=1\) with \(H\) the fixed compatibility
and target mask. The rest of the real integrand involves
only the physical \(m\), not its divided free integer.
The same strict short Mertens harmonic therefore applies.
In either case the fully transported model is
arbitrarily log-small. Restoring the previously paid
boundaries gives the asserted bound for the original
four genuine prime weights and the actual signed \(m\).
