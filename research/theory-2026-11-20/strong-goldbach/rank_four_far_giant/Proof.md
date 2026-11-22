# The genuine far-giant negative rank-four tail of the lifted shared-index score

This result uses the large-free ledger in [the near-half cutoff
lift](../rank_four_near_half/Proof.md), not the alternative medium-slot
subtraction. It gives a matching-order per-target estimate on an actual
negative tail and a per-common-index upper bound. It does not evaluate
the whole negative rank-four population or the full signed covariance.

Use the same definitions as in the near-half note: \(N=2x\) is a fixed
even integer, \(Y=\sqrt{x}\), \(L=\log x\), \(\ell=\log L\),
\(z=\exp(L/\ell^2)\), \(E=[.65Y,.8Y]\), \(I=[Y,1.1Y]\), and
\(\beta(e)\) counts the two literal prime tags on \(e\).
All physical slopes and common indices are units of \(N\).
Fix \(0<\eta<.01\), let \(T^\uparrow\) be the calibrated lifted cutoff
there, and write
\[
 R(y)=K(y)-F_{T^\uparrow}(y).
\]
For \(0<\epsilon\le10^{-3}\) fixed, set
\[
 H_\epsilon(k)=
 \sum_{\substack{e\in E,\ (e,N)=1\\
                  y=N-ek\ {\rm squarefree},\ \omega(y)=4\\
                  P^+(y)\ge x^{.766-\epsilon}}}
                  \beta(e)\,(-R(y))_+ ,
 \qquad
 \Delta_\epsilon=\epsilon^2(1+\log(1/\epsilon)).
\]
Here \(H_\epsilon\) is a nonnegative score on the **actual** negative
part, not an unsigned factorization count with a guessed sign.

**Conclusions, for sufficiently large \(x\) depending on the fixed
parameters.**
1. The score \(R(y)\) is identically zero on all \(y\in[x,3x/2]\)
with \(P^+(y)\ge x^{.766}\), without a rank or squarefree restriction.
2. For every actual unit common index \(k\in I\),
\[
                 H_\epsilon(k)\ll \frac{x}{\varphi(k)}\Delta_\epsilon .
                                                                    \tag{1}
\]
3. At each fixed even target the total tail has matching order:
\[
  \sum_{k\in I,\,(k,N)=1}H_\epsilon(k)
          \asymp x\,\frac{\varphi(N)}N\,\Delta_\epsilon .              \tag{2}
\]
The lower bound does not rely on a Goldbach representation.
4. Against the genuine opposite prime row
\[
 P(k)=\sum_{d\in E,\,(d,N)=1}
     \beta(d)\log(N-dk)\,1_{\{N-dk\ {\rm prime}\}},
\]
one obtains the **upper**, not lower, bound
\[
 \sum_{k\in I,\,(k,N)=1}P(k)H_\epsilon(k)
       \ll x^{3/2}\frac{\varphi(N)}N\,\Delta_\epsilon .                \tag{3}
\]
The same upper holds for an opposite row of absolute magnitude
\(O(x/\varphi(k))\). For the full opposite rough \(R\)-row,
the bound proved here has an additional factor \(\ell^8\).
In particular (2) is not a lower bound on the same-\(k\)
pairing with true primes or on the signed \(R\times R\) term.

## 1. The exact giant cutoff and directed charges

Let \(g=P^+(y)\). It suffices to consider \(z\)-rough \(y\), since
otherwise \(R(y)=0\). For \(g\ge x^{.766}\), it can occur only once;
all original \(s>1\) labels with \(r=y/s>x^{.505}\) exclude it.
Each such \(s\) is at most \(1.5x^{.234}\), and
\[
    y/g<T^\uparrow(s)\le x^{.766}s^{-1/2}<g .
\]
Indeed on this range the lifted floor is less than the original
first cutoff \(x^{.766}s^{-1/2}\), and the wider annular cutoff is
never larger than the first. The lower inequality also follows
from the lifted floor \(T^\uparrow(s)\ge x^{.505}\).
Thus an accepted free divisor \(a\mid r\) is exactly a divisor
containing \(g\). The accompanying \(c\)'s are exactly the divisors
of \(r/g\), and
\[
 \sum_{c\mid r/g}\mu_2(c)
    =(\mu*\mu*{\bf1})(r/g)=\mu(r/g)=-\mu(r).
\]
This proves cancellation for each admitted \(s\), even on
nonsquarefree \(y/g\). The \(s=1\) label has zero weight.
In fact the same full cancellation applies if
\(g\sqrt{P^-(y)}>x^{.766}\): for composite \(y\) this implies
\(g\ge(2/3)x^{.532}\) by \(P^-(y)\le y/g\), hence
\(y/g\ll x^{.468}<x^{.495-\eta}\).
The lifted floor is still below the first cutoff on the entire
non-giant \(s\)-range and above \(y/g\); the displayed
inequality \(T^\uparrow(s)<g\) now follows from \(s\ge P^-(y)\).
For prime \(y\) the claim is immediate.

Now consider squarefree rank four \(y=g p_1p_2p_3\) in the
far-giant window of the theorem. Every subset of the three
small primes is an admitted original \(s\)-label; no \(s\)
containing \(g\) is admitted. For every such \(s\) the free
cutoff exceeds \(y/g\), so all accepted free divisors contain \(g\).
If \(T^\uparrow(s)<g\), the whole label cancels as above.
For a singleton \(s=p_i\) with \(T^\uparrow(p_i)\ge g\), the
raw \(r\) has rank three, and the \(c=1\) part cancels its
raw \(\mu(r)\). Each other negative term, with \(c=p_j\),
has weight \(-2\log p_i\) and occurs precisely when
\(g p_\nu>T^\uparrow(p_i)\) for the remaining small prime
\(p_\nu\). There are no other terms: \(c=p_jp_\nu\) would
give the rejected free \(a=g\). For a pair \(s=p_i p_j\),
its nonnegative score is \(2\log(p_i p_j)\) if
\(T^\uparrow(p_i p_j)\ge g\), and zero otherwise.
This pair pays both possible directed singleton charges
\(i\to j\) and \(j\to i\) whenever it is positive.
The triple \(s\)-label has raw \(r=g\) and zero score.
It follows that the actual negative part is bounded by the
sum of \(2\log p_i\) over **unpaid** directed triples, satisfying
\[
      T^\uparrow(p_i p_j)<g\ \le T^\uparrow(p_i)<g p_\nu .            \tag{4}
\]
All strict inequalities here come from the literal strict cutoff
in the free factor.

Write \(v=\log g/L\), \(b=.766-v\), and let
\(a,\ c,\ d\) be the exponents of \(p_i,p_j,p_\nu\), respectively.
For (4), \(0\le b\le\epsilon\).
Since \(T^\uparrow(p_i)\) is at most the first cutoff
\(x^{.766}p_i^{-1/2}\) on the entire non-giant range, one has
\(a\le2b\le.002\). Thus the cutoff at \(p_i\) is exactly the
first cutoff, and \(d>b-a/2\).
If \(a+c<.13\), the cutoff at \(p_i p_j\) is also the first,
so \(c>2b-a\). If \(a+c\ge.13\), this last inequality
still holds because \(c\ge.13-2\epsilon>2\epsilon\).
In particular all unpaid terms satisfy
\[
               0<a\le2b,\qquad c>2b-a,\qquad d>b-a/2 .             \tag{5}
\]

## 2. The upper bound at each actual common index

Fix an actual \(k\) and the other three genuine primes with product
\(D=p_i p_j p_\nu\). If \((D,k)>1\) there is no physical term, since
\((k,N)=1\). Otherwise the giant is in the reduced residue
\(N\overline D\bmod k\). The progression endpoint is at most
\(1.5 x/D\), and \(x/D\gg x^{.766-\epsilon}\).
The classical Brun–Titchmarsh inequality gives at most
\[
                  O\!\left(\frac{x}{D\varphi(k)L}\right)
\]
true giant primes, uniformly in \(k,D\) and in \(0<\epsilon\le10^{-3}\).
Indeed \(\log((1.5x/D)/k)\gg L\).
Each giant gives at most one slope \(e\), and \(\beta(e)=O(1)\)
in the two fixed exponent bands. We can drop the extra physical
constraints for this upper bound, but must retain the existence of
some \(y\in[x,3x/2]\) satisfying (5).
Multiplying by the weight \(2aL\) reduces (1) to a harmonic
sum of \(a/D\) under those necessary inequalities.

Here are uniform endpoint details for that harmonic estimate.
Let \(b_0=a+c+d-.234\), and \(t=\log y/L\).
Then \(b=b_0-(t-1)\) with \(0\le t-1\le\log(3/2)/L\).
Therefore \(b_0\in[0,\epsilon+O(L^{-1})]\), \(a\le2b_0\),
and both \(c,d\) are at least a fixed constant times
\(\max(\ell^{-2},2b_0-a)\), using actual roughness.
For example if \(2b_0-a\ge8\log(3/2)/L\) this follows
directly from (5); otherwise the roughness cutoff suffices.
The sum of \(c,d\) is \(.234+b_0-a\), bounded away from zero.

Partition each positive prime variable into ordinary dyadic
intervals. For exponent mesh \(h=(\log2)/L\), the reciprocal
prime mass in one cell at exponent \(q\ge\ell^{-2}-h\)
is \(O(h/q)\), uniformly, by the elementary prime-count
upper bound for a dyadic interval. The charged \(a\)-cell
has mass \(O(h)\) after its weight \(a\).
Consequently the enlarged angular integral upper bound has
measure \(da\,dc\,dd/(cd)\).
Use coordinates \((b_0,a,c)\), eliminating
\(d=.234+b_0-a-c\); this change has Jacobian one.
For fixed \(b_0,a\) the \(c\)-integral is
\[
 O\!\left(1+\log^+\!\frac{1}{\max(\ell^{-2},\,\kappa(2b_0-a)_+)}\right)
\]
for an absolute constant \(\kappa>0\), because \(c+d\)
is bounded away from zero. Widening all boundaries by \(O(h)\)
only adds a strip \(a>2b_0-O(h)\) of cost
\(O_\epsilon(h(1+\log\ell))=o(1)\) after regularization.
On \(0<a<2b_0\), we may use \(O(1+\log(1/(2b_0-a)))\),
an integrable envelope. Integration over \(0<b_0<\epsilon\)
and \(0<a<2b_0\) gives \(O(\Delta_\epsilon)\).
The \(o(1)\) endpoint error is harmless for each fixed \(\epsilon\).
This proves (1).

## 3. A matching genuine fixed-target lower

Choose true prime exponents in the open region
\[
 \tfrac12\epsilon<b<\tfrac34\epsilon,\qquad
 b/3<a<2b/3,\qquad 3b<c<.02,\qquad
 d=t-(.766-b)-a-c .
 \tag{6}
\]
All four factors have distinct sizes, and
\(d\in(.21,.24)\) for the physical \(t=1+O(1/L)\).
Restrict to \(e\in[.70Y,.71Y]\) and
\(y\in[1.24x,1.27x]\). Then the corresponding \(k=(N-y)/e\)
is in \(I\) for every such \(e,y\).

In (6), the only nonzero singleton score or pair score is
the negative label \(s=p_i\) of exponent \(a\). Indeed
its free cutoff is \(T_1(p_i)\), lying above \(g\)
but below either \(g p_j\) or \(g p_\nu\), so it contributes
exactly \(-4aL\). The cutoff at the \(c\)-prime and at the
pair of exponents \(a+c\) is below \(g\) since \(c>3b\).
Every label containing the \(d\)-prime is in the wider
\([.13,.32]\) cutoff band and has cutoff below \(g\).
The triple-complement score is zero. Thus this open region
has true sign and true weight, not just a negative labelled
summand that could be canceled on the same integer.

For this lower bound, open the **slope modulus \(e\)**, summing the
physical common \(k\). This is not the modulus \(k p_2p_3\) used
for the per-\(k\) upper. In each independent log-fine
factor box use [Fouvry, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
with the true shortest prime of exponent \(a\) as the
short Siegel–Walfisz coefficient and the other three true primes
grouped as the long coefficient. Their exponent bands are
distinct, so the grouped coefficient is bounded in each
independent box. The fixed residue is the actual integer \(N\);
on supporting fine boxes \(N\le 4M_0N_0\) with \(M_0,N_0\) the
respective short and long dyadic anchors. The applicable full
modulus \(e\asymp x^{1/2}\) is below both power bounds
\(x^{1/2+a/2}\) and \(x^{4/7-6a/7}\) by a fixed margin,
since \(a\) belongs to a fixed compact subinterval of
\((0,10^{-3})\) for each fixed \(\epsilon\).
Its arbitrary order-divisor testing gives the absolute
discrepancy including the bounded true \(\beta(e)\).
All factor slots can omit the prime factors of \(N\),
retaining the physical \((y,N)=1\); the omissions in their
harmonic models are uniformly negligible.
One can use smooth minor cutoffs supported strictly inside (6)
and the fixed \(y\)-interval. Separating on log-fine independent
factor boxes then costs fixed log powers; the positive
principal is unchanged to the required asymptotic precision.
No source with a composite primality surrogate is used here.

After the reduced progression main, ordinary PNT in the
longest genuine prime and reciprocal prime summation in
the other three slots give angular measure proportional to
\[
                        \frac{da\,dc\,dd}{c\,d\,v}.
\]
The \(a\)-denominator disappears because the actual score is
\(4aL\), and the \(vL\) cost is the prime density of the
longest slot. Polynomial prime divisors of \(e\) have
uniformly negligible reciprocal effect in all four slots,
including in the longest prime model.
With \(db=dd\) at fixed \(a,c,t\) and \(d,v\) bounded
away from zero, the mass in (6), even on slightly smaller
open intervals, is
\(\gg \epsilon^2(1+\log(1/\epsilon))\).
This follows by integrating \(c\) from a fixed multiple of
\(\epsilon\) up to a fixed small constant, and using fixed
multiples of \(\epsilon\) for the \(b\) and \(a\) lengths.
The modulus principal is \(1/\varphi(e)\) times the true
independent model, and
\[
 \sum_{\substack{.70Y\le e\le.71Y\\(e,N)=1}}
       \frac{\beta(e)}{\varphi(e)}\gg\frac{\varphi(N)}N .
\]
For this, count the free cofactor of each actual tag pair by
inclusion–exclusion, then sum the positive reciprocal-prime
mass in the two fixed tag bands. All physical \(k\)'s are
automatically units on the retained actual target mask.
Thus the lower bound in (2) follows with the true sign at
each integer of this region. This procedure does not prove
a uniform positive lower in \(k\).

## 4. Opposing row envelopes and limits

The genuine prime row \(P(k)\) is \(O(x/\varphi(k))\) by the
same Brun–Titchmarsh bound at the macroscopic prime scale,
including \(\log y\) and the bounded weight \(\beta(d)\).
Also
\[
 \sum_{k\in I,\,(k,N)=1}(k/\varphi(k))^2\ll Y\varphi(N)/N .
\]
Indeed the square is a positive squarefree divisor sum with
local coefficient \((1-1/p)^{-2}-1\ll1/p\).
Truncate the divisor at \(Y^{1/10}\), count unit multiples
by inclusion–exclusion, and pay the tail using the convergent
positive reciprocal divisor moment with any fixed exponent
below one. The same first-power argument sums (1).
These facts prove the upper sides of (2) and (3).

For the opposite full rough residual,
\(|R(y)|\ll L R_z(y)\tau_4(y)\) pointwise by the exact divisor
formulas. Shiu's bound on the physical reduced class
\(N\bmod k\), for its interval of length \(\asymp x\), gives
an absolute row bound \(O((x/\varphi(k))\ell^8)\).
Indeed the multiplicative majorant \(R_z(n)\tau_4(n)\)
has \(f(p)=4\) for \(p>z\) and zero for \(p\le z\),
and the exponential prime factor in Shiu is
\(\exp(4\sum_{z<p\le 2x}1/p+O(1))\ll\ell^8\).
Thus (3) transfers to that absolute row only with this
explicit loss. No arbitrary-log or signed estimate of
the full \(R\times R\) covariance follows. The near-half
and middle large-prime negative regions, and ranks
at least five, are not evaluated by this tail calculation.

