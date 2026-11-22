# A central rough Chen bound and the corresponding true parity test

Let \(N=2x\) tend to infinity through even integers, \(L=\log x\),
and \(J=xJ_0\), where \(J_0\subset[1,4/3]\) is any fixed interval
of positive length. Let \(P=N-y\), \(M=|J|\mathfrak S(N)\), with
\(\mathfrak S\) the ordinary binary Goldbach singular series.
In what follows \(P\) is a **genuine prime**. Give every counted
row weight \((\log P)(\log y)\). Let \(G_J(N)\) denote the weighted
sum with \(y\) prime, and \(C_{2,J}(\alpha;N)\) that with \(y\)
a product of two distinct primes both exceeding \(x^\alpha\).

**Unconditional pointwise bounds.** For every sufficiently large even
\(N\),
\[
 \begin{split}
 G_J(N)+C_{2,J}(.265;N)&>.032\,M,\\
 G_J(N)+C_{2,J}(.2663;N)&>.0036\,M.                          \tag{1}
 \end{split}
\]
In particular a target with no binary prime representation must
have the indicated natural-scale genuine prime-plus-semiprime mass
in **every fixed central interval** of this type, with both semiprime
factors polynomially large. The proof does not itself exclude this
alternative. The cutoff in (1) is in units of \(x=N/2\); for a
cutoff \(N^\gamma\), take any fixed \(\gamma\) strictly below the
corresponding exponent.

**Same-target criterion, not established.** At \(\alpha=.265\)
use the actual parity sum
\[
 T_J(N)=\sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
             y\ {\rm squarefree},\ P^-(y)>x^{.265},\
             P^+(y)>x^{.48}}}(\log P)(\log y)\lambda(y).
\]
The support is exactly the prime and semiprime support in the
first line of (1): the rough condition permits at most three
factors, a true triprime has largest factor
\(\le(4/3)x^{1-2(.265)}<x^{.48}\), and the largest factor of every
semiprime here is at least \(\sqrt{y}\ge\sqrt{x}\).
Thus \(T_J=C_{2,J}(.265;N)-G_J\) exactly.
In particular the new pointwise input \(T_J(N)\le .031 M\)
would imply \(G_J(N)>.0005M\).
The corresponding true dyadic mean of \(T_J\), normalized by
\(\sum M\), is between \(.020\) and \(.021\), so this proposed
upper is not contradicted by averaging. No pointwise upper on
this signed \(T_J\) is asserted. An upper on the positive
semiprime count alone would demand a different, much larger
subtraction; the ordinary semiprime reference exceeds \(M\).

**Scope.** [Ratliff, May 25, 2026, v2](https://zenodo.org/records/20377091)
claims an exponent just above .2665, for a related one-start
Buchstab calculation with modified weights and a marked
switched lower on the product-prime source. We do not use
that claimed bound, its marked switched input, or priority
over it. Here every compulsory first prime in the unswitched
branch satisfies a literal checked all-prefix square test
before ordinary independent packing; when that test may fail
we use ordinary sub-root BV instead. The exact triprime
contamination is paid using the separately verified [3.446
actual angular upper](../angular_prime_first_composite/Proof.md)
on the real prime opponent. The numerical result (1) and its
signed criterion are for the same fixed central \(J\).
We do not claim the upper from that earlier note on a shrinking
spatial window merely because the distribution input permits
variable prefix endpoints.

## 1. A base lower at \(\beta=25/224\)

For a roughness threshold \(z\), write \(S_J(z)\) for the literal
\(L\log P\)-weighted sum over \(y\in J\) with \(P^-(y)>z\).
We omit target nonunits throughout. On actual central
prime rows these would require \(P\mid N\) and cost \(O(L^2)\).
All arithmetic moduli below have the one reduced residue
\(N\bmod q\) on \(P\), not a small-modulus stand-in.

Let \(\beta=25/224\), \(D_0=x^{.5557}\).
We prove
\[
 \frac{S_J(x^\beta)}M\ \ge\
        b_0+o(1),\qquad
 b_0=\frac{e^{-\gamma}}{\beta}
                 f(.5557/\beta),                             \tag{2}
\]
with the usual one-dimensional linear-sieve lower function.
For the short and long banks, use the same honest ordinary
weight comparison as in
[the reflected low-rank reserve](../overmarked_rough_low_rank_reserve/Proof.md):
a sufficiently small fixed power bound \(x^\xi\) between
the banks, fundamental-lemma upper/lower \(H_s,L_s\) of level
\(x^b\) on primes below it, and ordinary Rosser \(H_l,L_l\)
of level \(D_0\) on the others. For the true avoidance
indicator the pointwise lower is \(L_s H_l+H_s L_l-H_sH_l\).
Indeed the two upper factors are nonnegative, and replacing
the lower factors by the true separate indicators leaves an
error equal to the negative of the product of the two
nonnegative upper errors. We omit primes dividing \(N\) from
both banks. On actual target units they cause no change.

The ordinary lower Rosser tests are the first square and
the even cubic prefix tests. They imply the all-prefix square
tests: at odd positions after the first, use the preceding
even cubic and monotonicity of the decreasing labels. The
first-square test is automatic at \(\beta\).
Here and below round the angular exponents upward on a fine
fixed mesh in prefix tests. This only rejects branches at
the correct even (lower) or odd (upper) locations. The
rejected subtree contribution has the sign of that branch,
as the product of its divisibility indicator and the exact
avoidance indicator for its remaining smaller primes.
The new lower/upper bounds are thus pointwise. The arithmetic
coefficients on each admitted bin vector now separate; the
difference between the exact and rounded harmonic models is
\(o_\Delta(1)\), since the large bank starts at a fixed
\(\xi>0\) and only finitely many prefix walls are involved.
Where several labels inhabit the same bin, divide by their
factorial permutation multiplicity after allowing independent
positions. Artificial repeated primes in these positions
cost a power by counting true multiples of their squares
(\(\gg x^{2\xi}\)) with fixed divisor multiplicities, and by
their reciprocal square harmonic in the principal.

We verify the spectral packing on the literal large-bank
support. Use [Lichtman, arXiv:2309.08522v1,
Propositions 5.2 and 6.1](https://arxiv.org/html/2309.08522v1#S6),
with \(\theta=7/32\), residue height exponent \(a_*=1.00001\),
and notional level \(d_*=.55572\).
Write
\[
 \Theta(t)=\min\left\{\frac{1+t}{2},
       \frac{1-(3/2-2\theta)t}{1+\theta},
                       1-\frac{a_*\theta+3t}{2}\right\}.
\]
Let \(u_*=.1115\).
If the largest label \(t_1\in[u_*,\beta]\),
each of these three entries is \(>d_*\).
If \(t_1<u_*\) with at least three labels, the \(w\)-branch
of (6.4) is allowed: \(t_1<\mu\) there, all three inner entries
exceed both \(d_*\) and \((1+u_*)/2\), and
\(t_2,t_3\le u_*\).
These comparisons hold with fixed margins, and are checked in
[the rational certificate](check.py).
Fewer than three labels in that case have full modulus
\(\le x^{2\beta+b+o(1)}\), covered by ordinary BV.

For clarity about applying the packing: decompose the genuine
prime source \(\Lambda(P)\) using order-three Heath–Brown,
inserting \(z_0=x^{1/(\log\log x)^3}\)-roughness, which is exact
on central primes; proper prime powers contribute
\(x^{1/2+o(1)}\) even with the fixed divisor-power weights
from the actual moduli. For a polynomial medium source slot
of length \(A'=x^{[2\tau,\,1/3+\tau/4]}\), take \(A=A'x^{-\tau}\)
in Proposition 6.1. As in the cited reserve, the selected
rough \(1,\log,\mu\) slot has auxiliary-mask Siegel–Walfisz.
Trim the grouped complementary divisor-bounded coefficient
with the arbitrary-log reserve from fixed divisor moments.
Assign the three modulus groups at one feasible representative
of each finite rounded bin vector and use the same index
groups throughout the box; choose its mesh sufficiently
fine compared to the packing slack. Merge the independent
small-bank factor into the third group, taking \(b\ll\tau\).
Making \(A\) into \(A'\) spends \(2\tau,\tau,(1+2\theta)\tau\)
in the three inequalities respectively; (6.3) left
\(3\tau,3\tau,2\tau\), before the arbitrarily smaller
bank and mesh losses. Thus the actual Proposition 5.2
with the factor \(|N|^\theta\) applies. Whole-product
intervals are removed by its Lemma 4.2, uniform in their
two endpoint values. If no medium slot is present, there
are one or two long free slots and remaining product
\(\le x^{12\tau+o(1)}\). For two use uniform-residue
Proposition 3.2 below the \(2/3\) rail; for one use the
ordinary CRT rough count via the fundamental lemma on
\(z_0\), as in the cited reserve (with its absolute floors
saving a fixed power at every modulus below .60 here).
In the two-free case the residue after freezing the short
product is a reduced class, with no small representative
assumed. These steps give logarithmic savings of arbitrary
fixed order after all selected modulus labels. The same
arithmetic treatment will be used for the marked upper
below. No general interval of arbitrary factorable
coefficients has been asserted without a packing.

After reassembly the exact principal for a modulus \(q\)
is the weighted prime mass \((1+o(1))|J|/\phi(q)\), since
central source primes exceed the moduli. The local product is
\[
 V_N(z)=\prod_{\substack{r\le z\\r\nmid N}}
          (1-1/(r-1))
      =(1+o(1))\frac{e^{-\gamma}\mathfrak S(N)}{\log z}
 \quad(z=x^{\text{fixed positive exponent}}),
\]
uniformly in \(N\); compare the ordinary Mertens product,
its convergent off-target quadratic corrections, and
the target-supported factors, including 2. Primes dividing
\(N\) above \(z\) cost \(1+o(1)\) relatively.
The fundamental-lemma ratios of the separate small bank
approach 1 by taking \(\xi\ll b\) after the margin.
With the correct ordinary normalized lower sieve function,
the rounded coefficient model approaches that in (2).
This proves the required lower in the successive parameter
limit (or with any fixed prescribed absolute tolerance).

## 2. The forced-prime branch, including its first square

Let \(s_*=.00005\), \(t_c=.254\), and \(D_{\rm BV}=.4999\).
For \(\beta\le t\le\alpha\) define the **full modulus** exponent
\[
 \eta(t)=
 \begin{cases}
 \min\{(1+t)/2,\ 1-(a_*\theta+3t)/2\}-s_* ,&t<t_c,\\
 D_{\rm BV},&t\ge t_c.
 \end{cases}
 \qquad R(t)=\eta(t)-t,\qquad \rho(t)=\min(t,R(t)/3).             \tag{3}
\]
Buchstab's identity partitions \(S_J(x^\beta)-S_J(x^\alpha)\)
by the actual least prime \(p_1\) of \(y\), with
\(p_1\in(x^\beta,x^\alpha]\). It imposes
\(p_1\mid y\) and no smaller prime dividing \(y\). For each
small fixed exponent bin in \(t=\log p_1/L\), use a residual
upper Rosser sieve at a threshold no larger than \(x^{\rho(t)}\)
and level no larger than \(x^{R(t)}\) throughout the bin.
Concretely for bin \([a,b']\) choose the residual exponent
to be \(\inf_{[a,b']}\eta(t)-b'\) with an arbitrarily
small further margin, and the rough threshold equal to
the lesser of \(a\) and one-third of that exponent.
Hence eliminating the sieve factors below this threshold
is an honest **upper**. Split the bins at \(t_c\) and at the
two other fixed junctions below. Use the nonnegative
product of upper small- and large-bank weights.
Sifting primes are strictly smaller than the forced prime
\(p_1\); no independent treatment of a possible \(p_1^2\)
is required for the upper, since such rows may be retained.
The actual modulus is \(p_1d\) on the large bank, and
\(p_1de\) when merged with the independent small bank.

Here is the needed forced-prime support check.
For \(\beta\le t<t_c\), the middle entry of \(\Theta(t)\)
is larger than the maximum of the two displayed
entries in their lower envelope
(\(.599\ldots>.59765\ldots\)); the crossover is
\(\tau_*=(1-a_*\theta)/4\).
Thus \(\eta(t)\le\Theta(t)-s_*\), uniformly.
Crucially the actual **first prefix square**
\(p_1^2\) also satisfies \(2t<\eta(t)\) with a fixed margin.
For the decreasing branch the smallest margin is at
\(t_c\), where
\[
       \eta(t_c-)-2t_c
       =1-(a_*\theta+3t_c)/2-s_*-2t_c>.0015;
\]
for the increasing branch the smallest margin is at
\(\tau_*\) and is larger. For the residual upper
Rosser support, every prefix square is valid at
level \(x^{R(t)}\), from its odd cubic tests; adjoining
\(p_1\) before those prefixes adds exactly \(t\) to
each relevant bound, which stays below \(\eta(t)\).
With a fixed small mesh and a notional level slightly
above the chosen actual bin total, these are literal
hypotheses of Proposition 6.1 at the forced first
label, even if few residual labels appear.
The same \(\Lambda\) decomposition and packing
argument of §1 therefore applies, with maximum
level \(<.60\) and enough uniform positive slack.
For \(t\ge t_c\) we use **only** ordinary BV at
total \(.4999\) plus the much smaller independent
bank; no all-prefix claim is needed.

The conditional density of the genuine \(p_1\)-mark
in the progression main is \(1/(p_1-1)\); it is not
a separate free quotient distribution assertion.
The reduced residues and real sieve bank multiply it
by \(V_N(x^{\rho(t)})F(R(t)/\rho(t))\), where \(F\)
is the ordinary upper sieve function. Primes \(p_1\mid N\)
have power-small omitted harmonic weight since
\(p_1>x^\beta\); they were already excluded on true units.
Use prime harmonic measure \(dt/t\) and then let
the fixed mesh approach zero. We obtain
\[
        S_J(x^\alpha)\ge (b_0-H_\alpha+o(1))M,
 \qquad
 H_\alpha=\int_\beta^\alpha
         \frac{e^{-\gamma}F(R(t)/\rho(t))}{t\rho(t)}\,dt.        \tag{4}
\]
As in (2), arbitrarily small fixed approximation errors
can be paid before the sufficiently-large-\(N\) limit.
Only the upper is used for the subtracted Buchstab branch.

## 3. Exact rank-three upper and numerical closure

When \(\alpha>1/4\), at most three prime factors occur on
the rough \(y\in J\) for all sufficiently large \(x\).
Nonsquarefree such \(y\) are negligible: they are
multiples of \(r^2,\ r>x^\alpha\), hence
\(O(x^{1-\alpha}+\sqrt x)\) integers, also negligible
with the two logs. For the genuine squarefree triprime
rows apply the already established **3.446** fixed-target
positive upper with source weight \(L\) times the
indicator of the actual three-prime product in \(J\),
all labels \(>x^\alpha\). The fixed-angle profile can
be approximated from above by smooth envelopes, as all
three factors are polynomially large and the ordinary
profile boundaries have measure zero. Use exactly the
same spatial main \(M\), not the full interval without
the \(J\)-factor. In the true \(\log P\log y\)
normalization, the upper is
\[
 \bigl(3.446\,I_3(\alpha)+o(1)\bigr)M,\qquad
 I_3(\alpha)=\int_\alpha^{1/3}
       \frac{\log((1-2u)/u)}{u(1-u)}\,du.                       \tag{5}
\]
Indeed order its three genuine factors, choose the
smallest exponent \(u\), then integrate the middle
\(v\in[u,(1-u)/2]\) with density
\(du\,dv/[uv(1-u-v)]\); this yields (5).
Replacing \(L\log P\) by \(\log y\log P\) is
relative \(1+O(1/L)\) on the final positive counts.

For reproducibility let \(\bar f=e^{-\gamma}f\),
\(\bar F=e^{-\gamma}F\).
The usual delay equations give \(\bar F(r)=2/r\)
for \(r\le3\) in our range, and for \(3\le r\le4\)
\[
     r\bar F(r)=2+2\int_3^r\frac{\log(v-2)}{v-1}\,dv .
\]
For \(4<r<5\), as used in \(b_0\),
\[
 r\bar f(r)=2\log(r-1)+
        2\int_3^{r-1}\frac{\log(v-2)}{v-1}\log\frac{r-1}{v}\,dv.
\]
The junction where \(\rho\) changes from \(t\) to
\(R/3\) in (3) is \(t_0=(1-2s_*)/7\).
On \([\beta,t_0]\) substitute
\(r=(1-2s_*)/(2t)-1/2\) in (4), and integrate
the formula for \(\bar F(r)\) against \(2\,dr/(1-2s_*)\).
The resulting double integral becomes the same elementary
single log integral after interchanging its nonnegative
levels. For \(t\ge t_0\) the integrand of (4) is
\(2/[t(A-Bt)]\) in each of the three remaining intervals,
with literal residual \(R(t)=A-Bt\); its primitive is
\((2/A)\log(t/(A-Bt))\).
The checker uses monotone-factor rectangular lower and
upper bounds for the one log integral, left upper bounds
on the decreasing nonnegative integrand in (5), and exact
rational logarithm enclosures. The strict results are
\[
 \begin{split}
 b_0-H_{.265}-3.446 I_3(.265)&>.0324,\\
 b_0-H_{.2663}-3.446 I_3(.2663)&>.00367 .
 \end{split}
\]
Choose the packing, bank and finite angular
approximation tolerances inside the remaining strict
margins. Combine (4)–(5); subtracting the entire true
triprime sector leaves precisely \(G_J+C_{2,J}\).
This proves (1).

## 4. Normalization of the signed test

For completeness the stated mean check is an actual count
on targets, not an estimate at a single \(N\).
Over even \(N=2n\), \(X\le n\le2X\), the denominator
\(\sum M\sim3|J_0|X^2\): the mean of \(\mathfrak S(N)\)
on even numbers is 2 by its usual positive divisor
expansion, and partial summation supplies \(|J|=n|J_0|\).
This is also the area of the independent prime-product
counting region \(2\le (P+y)/X\le4\),
\(2y/(P+y)\in J_0\), multiplied by \(X^2\).
All genuine pairs counted here are odd–odd, so no extra
one-half occurs in their joint PNT count. Prime and
genuine semiprime weights on this region give, respectively,
the integrated factors \(1\) and
\(\int_\alpha^{1/2}du/[u(1-u)]\).
For the semiprime factor this follows by fixing the
real smaller prime in its compact angular band and using
PNT in the last factor, then its prime harmonic.
Approximate the fixed spatial polygon by rectangles;
the fixed angular boundaries have zero measure.
Thus the weighted dyadic mean of the **actual signed**
\(T_J\) at \(\alpha=.265\) is
\(\log((1-\alpha)/\alpha)-1\), strictly between .020 and .021
by the exact checker. This establishes only compatibility
of the .031 pointwise target with the true averaged
arithmetic. It does not bound that signed target on
the exceptional fixed even integers we need.
