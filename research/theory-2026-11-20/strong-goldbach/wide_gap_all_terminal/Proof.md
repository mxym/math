# Both-parity payment of the genuine all-rank terminal in a wider gap

This is a variant of the reciprocal [all-small completed score](../completed_gap_two_true_sectors/Proof.md),
not the original fixed-payer score. The wider gap is used for an
exact same-row orientation payment. Its full genuine prime mean
has the same all-completed calibration as in the
[many-small renormalization](../direct_many_small_renormalization/Proof.md).
The outer and safe signed residuals are not controlled by this payment.

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(z=x^\chi\) with \(\ell^{-2}\le\chi\le\ell^{-1}\),
\(J=xJ_0\subset[x,1.5x]\), and \(P=N-y\) genuine prime.
Put \(T_y=\log y/(2L)\), \(U=\ell^{-1/4}\),
\(R_\pm(y)=\sqrt y\,x^{\pm U}\), and \(C_y=y/x^{1-\epsilon}\).
For the orientation payment one can use fixed \(0<\epsilon<.005\);
the calibration also holds for a moving
\(\ell^{-\alpha}\le\epsilon\le.005\) for any fixed \(0<\alpha<1/8\).
Do not transfer other fixed-\(\epsilon\) sign results to this
moving range without a separate proof.

For a squarefree \(z\)-rough \(y\) use the all-completed score
with \(\mu_2(c)1_{P^+(c)<C_y}\) on every actual \(c\mid y\) in its
free term, no payer, and raw lower cutoff \(R_-(y)\).
For a short \(d<\sqrt y\) put \(t=T_y-\log d/L\) and \(v=y/d\).
When \(0<t<U\), the pair is raw-only with actual contribution
\[
                  C(y,d)=\mu(d)\log v+\mu(v)\log d.            \tag{1}
\]
In particular \(|C(y,d)|=\log y\) for even \(\omega(y)\),
and \(|C(y,d)|=2tL\) for odd \(\omega(y)\).
We call \(0<t<M\chi\) *terminal*, where \(9\le M\le(\log\ell)^B\)
for any fixed \(B\). No genuine factor-rank or factor-size
restriction is imposed on \(d\) or \(v\).

**1. Actual orientation payment.** Each squarefree \(z\)-rough
\(y\) outside explicit rare exceptions below admits disjoint
same-y groups of raw-only pairs which contain all its terminal
pairs, with exact total score zero on each group. Each group
contains exactly one terminal pair; all its other pairs lie
at depths \(>M\chi\) and \(<U\). Thus the terminal debit is
paid by the literal net score of its own outer receivers,
without asserting that net score is a new independent reserve.
The absolute cost of the exceptional terminal orientations,
after summing over genuine \(P\) and weighting by \(\log P\), is
\[
                  \ll x\mathfrak S(N)
                      \left(\frac{M^3\chi}{U^2}
                                   +\frac{M^4\chi}{U}\right)
                    +O_A(xL^{-A})
                   =o(x\mathfrak S(N)).                         \tag{2}
\]
This holds uniformly in the actual even target and \(\chi\).

**2. Actual calibration at this wider gap.** Write
\(Q_\epsilon(t)\) for the cumulative of the positive locally
finite convolution exponential \(\exp^*(2\,1_{u>\epsilon}du/u)\)
on \([0,\infty)\), including its unit atom at 0. For the
all-completed score \(\mathcal R^{\rm all}_{U}\) just defined,
\[
  \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
           \log P\,\mathcal R^{\rm all}_{U}(y)
    ={\cal G}_J(N)+|J|\mathfrak S(N)\bigl[Q_\epsilon(1/2)-1\bigr]
                       +o_{\alpha,J_0}(x\mathfrak S(N)).         \tag{3}
\]
For fixed \(\epsilon\) the constants may instead depend on
\(\epsilon,J_0\). In particular (3) is the calibration of this
changed gap, not an assertion that the gap score by itself
equals the binary prime count.

## 1. Exact toggle groups for both parities

For any genuine r dividing squarefree y, toggle its bit in a
divisor of y, and toggle it to the other leg of the complementary
pair. This is a well-defined involution on unordered complementary
pairs since divisor complement commutes with XOR of a prime bit.

For even \(\omega(y)\), choose the least actual y-prime r in the bank
\[
                      x^{3M\chi}<r\le x^{U/4}.
\]
If there is none, the row is exceptional in this parity.
For each terminal pair, toggle r. The new depth is one of
\(\log r/L+t\), \(\log r/L-t\), according to the actual
membership of r in the short leg. Both depths are \(>M\chi\)
and \(<U\) eventually. Both divisors stay raw-only before and
after the toggle. Either leg has the same Möbius sign when
\(\mu(y)=+1\); the toggle reverses it. Thus their scores
in (1) are exact opposites. An involution with a unique
terminal member in each such orbit supplies disjoint groups.

For odd \(\omega(y)\), require an actual prime in each of the
two banks with exponent intervals
\[
                  (3M\chi,\sqrt{\chi U}],\qquad
                  (2\sqrt{\chi U},U/4].
\]
If either is missing, the row is exceptional in this parity.
Otherwise choose the least actual prime r from the first,
and s from the second. The choices depend only on y, not
on the current short divisor. Let \(e_r=\log r/L\) and
\(e_s=\log s/L\). Each of \(e_r,e_s,e_s-e_r\) exceeds
\(3M\chi\) eventually, since \(U/\chi\) tends to infinity
faster than \(M^2\). Any nontrivial combination of
these two toggles changes the log of one originally
designated leg by one of \(\pm e_r,\pm e_s,\pm e_r\pm e_s\).
For a terminal pair the resulting absolute depth is therefore
\(>M\chi\) and is \(\le M\chi+e_r+e_s<U\).
The whole four-member orbit is genuinely raw-only.
The group action is free: neither individual tag nor their
product contains every prime of y, because their product
is \(<x\) while \(y\ge x\).

For clarity, evaluate (1) on one designated leg in each of
the four configurations rather than switching to the shorter
side; the expression is symmetric in the two legs. Its two
Möbius factors each change by \((-1)^{i+j}\) upon toggling
the two bits \(i,j\in\{0,1\}\), and both logarithms are
affine functions of \(i,j\). The second alternating
difference of an affine function vanishes. The sum of
the four actual scores is consequently zero. Every such
orbit contains exactly one terminal pair and the chosen
global tags make the orbits disjoint at each physical y.
For negative terminal score we use the literal net of all
three outer partners, including any of their negative values.

These groups are alternative allocations of outer scores.
The algebra does not give a bound on any actual collection
of outer pairs left over after deleting the groups, and
does not assert their positivity.

## 2. Actual bounds for the missing-bank orientations

The following genuine count does not condition on an
unproved parity law. Let \(\mathcal E\) be any one of the
displayed banks and \(B_{\mathcal E}=\prod_{r\in\mathcal E}(1-1/r)\).
An exceptional \(y\) with no \(\mathcal E\)-prime has both
physical d and physical v avoiding \(\mathcal E\).
They are also each \(z\)-rough. The terminal condition gives
\[
                     x^{1/2-M\chi}<d<\sqrt{1.5x}.
\]
By the ordinary one-dimensional upper sieve on integers
in each dyad in this range, the harmonic of such d is
\[
       \sum_{\substack{x^{1/2-M\chi}<d<\sqrt{1.5x}\\
                      d\ z\text{-rough},\ d\text{ avoids }\mathcal E}}
                            \frac1d
                   \ll M\,B_{\mathcal E}.                       \tag{4}
\]
Indeed the per-dyad density is at most
\(O(B_{\mathcal E}/(\chi L))\), and the number of dyads
is \(O(M\chi L+1)\). For example use a fixed Selberg divisor
level \(x^{.10}\) and maximal sifting prime at most \(x^{.01}\)
eventually. The square-expanded floor errors
\(O(x^{.20}L^{O(1)})\) are negligible on all these long dyads.

For every actual fixed d admissible in (4), the genuine
count on \(v\in[x/d,1.5x/d]\) of \(z\)-rough v avoiding
\(\mathcal E\) with \(P=N-dv\) prime is at most
\[
                       O\left(\frac{x\mathfrak S(N)}
                                     {d\,\chi L^2}
                                                B_{\mathcal E}\right). \tag{5}
\]
This is the literal two-form positive upper sieve from the
[narrow toggle](../terminal_tiny_core_toggle/Proof.md), here with
the full chosen avoidance bank rather than a randomized sub-bank.
If \((d,N)>1\), the only genuine P must divide N; at most
\(O(1)\) such actual y are admitted, with total \(x^{o(1)}\)
cost. Otherwise at small primes \(r\le z\) the two forms
have two roots except when \(r\mid N\), where they have one
(including 2); insertion of an additional r in the bank
adds one forbidden root for v when it is distinct.
The bank primes are \(>z\), so the local collision/omission
adjustments for any \(r\mid dN\) cost \(1+O(L/z)\) beyond
the truncated singular factor. Other primes up to \(x^{.01}\)
sieve P alone. The density is therefore
\(O(\mathfrak S(N)B_{\mathcal E}/(\chi L^2))\).
The same fixed sieve level \(x^{.10}\) and the long
free interval \(\asymp x/d\gg\sqrt x\) give the floor reserve.
This is a conditional upper for a real affine pair of forms,
not a product of two assumed prime marginals.
Squareful y can be omitted in the statement at arbitrary-log
cost by their \(O(x/z)\) true integer bound and fixed divisor
moments; no squarefreeness is needed in (4) or (5).

Using (4), (5) and the two log weights, any genuine missing-bank
even terminal contribution is
\(O(x\mathfrak S(N)M B_{\mathcal E}^2/\chi)\).
For the full even bank, prime Mertens gives
\(B_{\mathcal E}\ll M\chi/U\).
For a missing odd bank, its additional score factor \(t\ll M\chi\)
makes the analogous bound
\(O(x\mathfrak S(N)M^2 B_{\mathcal E}^2)\).
The two odd bank factors are respectively
\(O(M\sqrt{\chi/U})\) and \(O(\sqrt{\chi/U})\).
The union bound over the two missing odd banks, along with the even
bound, gives (2). Indeed for \(U=\ell^{-1/4}\),
\(\chi/U^2\le\ell^{-1/2}\) and \(\chi/U\le\ell^{-3/4}\).
Thus fixed powers of \(\log\ell\) in M are harmless.
All edge equalities can be discarded: each relevant actual
equality divisor determines y, hence gives at most a
power-small count by the divisor bound and log weights.

## 3. Calibration using the same completed physical score

We give the transfer because using the old \(\delta\)-guard
alone would not justify (3). On a squarefree rough y put
\(S_d(y)=\prod_{r\mid d,r<C_y}r\). The **complete** free term
for any actual divisor \(a>R_+(y)\) with \(d=y/a\) is
\[
             \sum_{c\mid S_d(y)}\mu_2(c)\log(d/c)
                 =\mu(S_d(y))(\log d-2\log S_d(y)).
\]
Here \(d<\sqrt y\,x^{-U}\). Using the exact full Möbius
logarithm identity on the raw branch, the entire score
therefore equals \(\Lambda(y)\) minus the short raw harmonic
weight \(\mu(d)\log(y/d)\) plus the short completed weight
above, each opened on \(d\le\sqrt y\,x^{-U}\); equality
differences are negligible as before. For the genuine
weight the proper powers in \(\Lambda(y)\) are negligible.
The complete squarefree-free envelopes are fixed divisor powers
and logs, even if \(\epsilon\) varies, and \(O(x/z)\) rough
squareful y can be dropped with Cauchy and fixed divisor moments.

Open the rough complement \(y/d\) by dimension-one upper and
lower fundamental lemma at level \(D=x^{U/2}\) with the
same density \(1/(p-1)\) on primes \(p\le z,\ p\nmid N\)
as in the [thin gap](../thin_true_giant_gap/Proof.md).
The modulus is literally \(dh\le\sqrt{1.5x}\,x^{-U/2}\).
The rough squarefree d and smooth h can be reconstructed
from this modulus by their disjoint prime ranges.
Both signed coefficients have size \(O(L)\); the free sign
and weight only jump at actual y-positions \(p x^{1-\epsilon}\)
for \(p\mid d\), and the raw log uses partial summation.
Thus maximal weighted ordinary BV applies with arbitrary
log reserve; the fundamental lemma is applied per sign
before cancellation. The parameter \(U/(2\chi)\gg\ell^{3/4}\)
makes its relative error smaller than every power of
\(1/\ell\), sufficient since the absolute main of either
short branch is \(O(x\mathfrak S(N)\chi^{-2})\).
The local factor is
\(V_N(z)=\mathfrak S(N)V_z(1+O(L/z))\); replace \(1/\varphi(d)\)
by \(1/d\) and delete target-prime masks on d's harmonic
at the same superlogarithmic costs as in the
[two signed sectors](../completed_gap_two_true_sectors/Proof.md).

Put \(D_y=T_y-U\), \(\epsilon_y=\log C_y/L\).
In the raw model, the cumulative of the signed harmonic
\(\mu(d)R_z(d)/d\) at log exponent t is
\(\rho_\chi(t)+O_A(L^{-A})\), where
\(\rho_\chi(t)=\rho(t/\chi)\) extended by zero to negatives.
This uniform quantitative prime harmonic comparison is
proved in the [two sectors, §2](../completed_gap_two_true_sectors/Proof.md).
It uses prime Mertens with tiny errors uniformly down to z
and keeps the unit atom at 1, not a limiting fixed-rank
replacement. Partial summation with \(\log(y/d)\), the
factorial bound for \(\rho_\chi(D_y)\), and
\(\int_0^\infty\rho_\chi=e^\gamma\chi\) give the raw
principal \(1+o(1)\) when normalized by \(|J|\mathfrak S(N)\):
the precise normalization is \(V_N(z)L/\mathfrak S(N)
\sim e^{-\gamma}/\chi\), with error saving arbitrary logs
after multiplying by the relevant harmonic scale.

For the free weight the signed harmonic value on an actual
rough prime factor is \(-1\) below \(C_y\) and \(+1\) above.
Its continuous measure is
\(\exp^*(-\nu_\chi+2\nu_{\epsilon_y})\), where
\(\nu_a=1_{u>a}du/u\). Marking \(\log d-2\log S_d(y)\)
multiplies the marked prime once more by its own sign, so
the marked slot is the positive Lebesgue measure
\(1_{u>\chi}du\), and has an extra factor \(L\).
The same prime-harmonic proof, with one marked slot, is
uniform even when \(\epsilon\) varies, since it just
moves one endpoint. Integrating the resulting density
up to \(D_y\) gives the free main divided by L exactly as
\[
            \int_0^{D_y-\chi}\rho_\chi(u)
                          Q_{\epsilon_y}(D_y-\chi-u)\,du.
\]
For \(t\in[.40,.60]\), \(Q_\epsilon(t)\ll\epsilon^{-2}\)
and its density is \(O(\epsilon^{-2})\).
Indeed the mass bound follows by exponentiating
\(\int_\epsilon^1 2\,du/u\), and for its positive density
\(q_\epsilon(t)\) one has
\(tq_\epsilon(t)=2Q_\epsilon(t-\epsilon)\) from marking
one slot in the convolution exponential.
Changing \(\epsilon\) by \(O(L^{-1})\) costs
\(O(1/(L\epsilon^3))\) in this cumulative, by telescoping
the two exponentials and bounding the change of one
prime interval by \(O(1/(L\epsilon))\).
The first moment \(\int u\rho_\chi(u)\,du\ll\chi^2\)
and its factorial tail now show that the normalized
free principal differs from \(Q_\epsilon(.5)\) by
\(O((U+\chi)\epsilon^{-2}+\epsilon^{-3}/L)+o(1)\).
This tends to zero also for \(\epsilon\ge\ell^{-\alpha}\),
\(\alpha<1/8\). The two principal signs are raw subtraction
and free addition. This proves (3).

The terminal payment uses actual raw pairs of the widened
score, while the already known signed smooth or marked
orientation estimates refer to a **gap-minus-own-root**
comparison. They cannot be combined by counting a receiver
twice. In particular (2) and (3) leave a true signed condition
on the exterior raw and safe rows relative to the nonzero
\(Q_\epsilon(.5)-1\) baseline, not an unconditional Goldbach
lower bound.
