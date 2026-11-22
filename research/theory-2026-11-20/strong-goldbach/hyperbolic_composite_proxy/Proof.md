# A hyperbolic composite prime proxy localizes every negative rank to two small primes

This note uses the literal two-free rectangle count from the
[full free-branch calculation](../full_free_hb_splice/Proof.md)
and the rough Möbius normalization from the
[endpoint evaluation](../full_endpoint_composite_proxy/Proof.md).
It gives a direct negative-prime-density formula for the
whole free score, not another centered model for only one cut.

Let \(N=2x\) be an even target, \(L=\log x,\ \ell=\log L,\ Y=\sqrt x\),
\(z=\exp(L/\ell^2)\), \(R=x^{.505}\), and
\(R_z(y)=1_{\{P^-(y)>z\}}\).
Fix \(0<\epsilon\le .082\) before \(x\) tends to infinity.
Write \(\mu_2=\mu*\mu\), and define
\[
 \begin{split}
 K(y)&=R_z(y)\sum_{\substack{sr=y\\r>R}}\mu(r)\log s,\\
 T_\epsilon(s)&=\max\{R,x^{1-\epsilon}/s\},\\
 F_\epsilon(y)&=-R_z(y)\sum_{\substack{sca=y\\a>T_\epsilon(s)}}
                                  \mu_2(c)\log s,\\
 R_\epsilon(y)&=K(y)-F_\epsilon(y).
 \end{split}                                                       \tag{1}
\]
The free-variable condition in (1) is exactly
\(a>R,\ c<y/x^{1-\epsilon}\); it implies the raw cutoff \(ca>R\),
without dropping the strict endpoint. In the original finite
Möbius expansion the free variable \(a>R\) is unique and all
remaining factors have product \(c\le1.5x^\epsilon<x^{.24}\).
Thus the short factors in that branch are unrestricted
and the branch coefficient is exactly \(-\mu_2(c)\).

**Direct progression theorem.** For every fixed
\(\delta,A>0\), every \(2\le Q\le x^{(2/3)(1-\epsilon)-\delta}\),
every reduced class \(j\bmod Q\), and every
interval \(J\subseteq[x,3x/2]\),
\[
   \sum_{\substack{y\in J\\y\equiv j\bmod Q}}F_\epsilon(y)
       =-\frac{|J|}{\varphi(Q)}
           +O_{\epsilon,\delta,A}((x/Q)L^{-A}).                    \tag{2}
\]
In particular the exponent is \(.612-\delta\) at
\(\epsilon=.082\). This is an arithmetic statement for a signed
composite score, not a PNT for genuine primes to these moduli.

**Tagged application.** In the original two-tag box from the
endpoint proof, the columns of \(R_\epsilon\) match the true
tagged log-prime columns in absolute \(k\)-sum with error
\(O_{\epsilon,A}(xL^{-A})\). The arbitrary-opposite-divisor-weight
transfer and the corrected covariance, including the negative
constant term \(-\sum_k M(k)^2\), remain valid with \(R_\epsilon\).

**Exact sign.** For all squarefree \(y\in[x,3x/2]\),
\(R_\epsilon(y)\) is nonnegative whenever \(y\) has **at most one**
genuine prime strictly below the moving cutoff \(y/x^{1-\epsilon}\).
In the no-small-prime case its nonnegative formula is
\(2R_z(y)\sum_{sr=y,\ r>R,\ \omega(r)\ {\rm even}}\log s\).
The score vanishes on primes and squarefree semiprimes.
For every fixed \(0<\epsilon\le10^{-3}\), there is nevertheless
a true negative squarefree rank-four family of logarithmically
weighted tagged mass \(\gg x\varphi(N)/N\) at each sufficiently
large fixed target. Its two small prime exponents are of order
\(\epsilon\); the lower-bound constant can be taken independent
of \(\epsilon\) in that range, with the starting threshold
allowed to depend on \(\epsilon\). Thus shrinking a fixed
\(\epsilon\) does not by itself bound the adverse mass.

## 1. Direct fixed-class evaluation of \(F_\epsilon\)

Put \(\xi=.10\) and \(C_y=y/x^{1-\epsilon}\).
For the short \(s\)-part \(s\le x^\xi\), in every allowed term
\(c<C_y\le1.5x^\epsilon\) and
\(a=y/(sc)\gg x^{1-\xi-\epsilon}\), so \(a>R\)
holds automatically. Keep the true rough \(s,c\) and open
roughness only on the genuinely free \(a\) by Bonferroni
through \(\lceil C\ell\rceil\) factors.
For \((sc,Q)=1\) the modulus is the actual reduced \(Q\),
with residue \(j\overline{sc}\); for a squarefree Bonferroni
divisor \(m\) coprime to \(Q\), the additional divisibility
changes the free interval count to length divided by \(mQ\)
with at most one floor error.
The finitely many such \(m\)'s are \(x^{o(1)}\); the
\(\tau(c)\log s\) weight and all \(s,c\) pairs contribute
\(x^{\xi+\epsilon+o(1)}\) to this floor error, a fixed
power below \(x/Q\) on the whole stated range.
The next-degree factorial error is treated by the same
positive count and the harmonic factorial tail, giving
arbitrary-log precision.

The short-part main, after substituting \(y=sca\), contains
the exact factor
\[
   \sum_{\substack{c<C_y\\(c,Q)=1}}\frac{\mu_2(c)R_z(c)}c ,
\]
independent of the short \(s\) once \(y\) is fixed.
This is \(O_{\epsilon,A}(L^{-A})\) uniformly by the
zeroth rough harmonic moment at the polynomial endpoint
\(C_y\). The true rough \(s\)-weight \(\log s/s\)
is left unchanged, with harmonic size \(O(L^2)\).
So the entire short part is negligible on the \((x/Q)\) scale.
No continuous approximation to rough numbers of a very short
\(s\)-scale is used here.

For \(s>x^\xi\), fix \(c\), leaving its true rough and
\(\mu_2(c)\) coefficient intact.
The product interval is \(y\in J\cap(c x^{1-\epsilon},\infty)\),
and the two individual sharp endpoints are \(a>R\) and
\(s>x^\xi\). Open independent Bonferroni divisors for the
roughness of \(a,s\); both remaining integers are genuinely
free, constrained by the unit-class product congruence.
On any box the difference between the true roughness
product and the two polynomials is bounded by
\(E(a)+E(s)+E(a)E(s)\), with \(E\) the next positive
factorial polynomial. Count each of these via the very
same two-free rectangle estimate. All floor and sieve
estimates are therefore uniform for a fixed \(Q,j\), not
averaged across target or modulus.

Use independent relative log-fine boxes in \(a,s\)
after dyadic subdivision. All unresolved endpoint boxes
have product or coordinate width \(O(L^{-B})\) relative,
so the same positive two-free count pays them. For each
\(c\) the principal area of a product boundary is
\(O(xL^{-B}/c)\) per dyadic box; the coordinate endpoints
cost the same by integrating the other variable.
Exact \(\log s\) weights may be retained by partial
summation. The positive sieve factorial tails are
arbitrary-log, and the pointwise divisor bounds cost only
\(x^{o(1)}\) in the power-error terms.

The first complete error of the rectangle count after
summing the \(c\)'s is \(x^{\epsilon+o(1)}Q^{1/2+\nu}\)
for arbitrarily small fixed \(\nu>0\).
It saves a power relative to \(x/Q\) precisely on the
stated \(Q\)-range, since \(\epsilon+3\log_x Q/2<1\)
with fixed margin. For a common \(c\)-scale \(C\) and
free scales \(S,W\), one has \(CSW\asymp x\).
The second rectangle error is thus bounded by
\(x^{o(1)}(x/S+x/W)Q^{-1+\nu}\), and saves a power
because \(S\ge x^\xi/2\) and \(W\ge R/2\).
This proves the asserted arbitrary-log total estimate
relative to the exact long-\(s\) principal.

Let \(W_z(Q)=\prod_{p\le z,\ p\nmid Q}(1-1/p)\).
The long-\(s\) principal has factor
\(\varphi(Q)W_z(Q)^2/Q^2\). At each \(c<C_y\)
and fixed physical \(y\), the literal interval
\(x^\xi<s<y/(cR)\) is nonempty and contributes
\[
 \int_{x^\xi}^{y/(cR)}\frac{\log s}{s}\,ds
     =\tfrac12\bigl[(\log(y/R)-\log c)^2-(\xi L)^2\bigr].
\]
The Jacobian from the \(a\)-integration contributes \(1/c\)
to the \(c\) coefficient. Define
\[
 B_Q(w)=\prod_{\substack{p\le z\ {\rm or}\ p\mid Q}}
                     (1-p^{-1-w})^{-1}.
\]
The three partial harmonic moments \(j=0,1,2\) of
\(\mu_2(c)R_z(c)1_{(c,Q)=1}(\log c)^j/c\)
at \(c<C_y\) are, respectively,
\(0,0,2B_Q(0)^2\), up to \(O_{\epsilon,A}(L^{-A})\).
Indeed their Dirichlet series before differentiating is
\(\zeta(1+w)^{-2}B_Q(w)^2\).
The uniform rough Perron shift and its first two
differentiations are as in the endpoint proof:
at fixed \(\epsilon>0\) the vertical error gains
\(\exp(-c\epsilon\ell^2)\); the finite Euler factors
are log-bounded uniformly in \(Q\), and standard
Perron cutoff errors are arbitrary-log from
\(|\mu_2(c)|\le\tau(c)\) and the short-interval divisor bound.
The first two vanishing moments kill all the
linear, quadratic-constant and lower-\(s\) terms in the last integral,
leaving exactly \(B_Q(0)^2\).
The **negative** sign of \(F_\epsilon\) yields
\[
 -\frac{\varphi(Q)W_z(Q)^2B_Q(0)^2}{Q^2}|J|
                 =-\frac{|J|}{\varphi(Q)}
\]
since \(W_z(Q)B_Q(0)=Q/\varphi(Q)\) exactly.
This proves (2).

In the physical box \(Q=kp_2p_3\le x^{.6092}\).
Restoring \((y,N)=1\) is arbitrary-log even per modulus
by the same count of actual rough values divisible by some
\(p>z\) dividing \(N\), followed by Shiu and Cauchy on their
same reduced progression. Thus the column of \(F_\epsilon\)
is \(-M(k)+O_{\epsilon,A}(YL^{-A})\), with \(M(k)\)
exactly as in the endpoint proof, including shared tag primes
of \(k\). That proof independently gives
\(\Gamma_{b_z}(k)=M(k)+O_A(YL^{-A})\).
The earlier
[above-root transfer](../overroot_shared_k/Proof.md)
matches \(\Gamma_K\) with the true centered
\(\Gamma_a-\Gamma_{b_z}\) in absolute \(k\)-sum.
Combining these three facts gives the asserted
transfer to \(\Gamma_a\) and the unchanged centered covariance,
with the same fixed divisor envelopes and log clipping.
The sign of the actual deviations around \(M\) remains unknown.

## 2. The exact one-small-prime positivity

For any \(m\) put
\[
               S(m)=\sum_{\substack{a\mid m\\a>R}}\log(m/a).
\]
Equation (1) gives the pointwise identity
\[
 R_\epsilon(y)=K(y)+R_z(y)
                \sum_{\substack{c\mid y\\c<C_y}}\mu_2(c)S(y/c).
                                                                    \tag{3}
\]
If no prime factor is below \(C_y\), only \(c=1\) occurs.
On squarefree \(y\) the result is then
\(R_z(y)\sum_{a\mid y,a>R}(1+\mu(a))\log(y/a)\ge0\).

If there is exactly one such prime \(p\), put \(m=y/p\).
For squarefree \(y\), the only allowed \(c\)'s are
\(1,p\), with weights \(1,-2\). Thus, on the rough set,
the score is \(K(y)+S(y)-2S(m)\).
For each \(a\mid m\) with \(a>R\), both \(a\) and \(pa\)
are admitted in the \(y\)-sum. Their paired contribution,
less the comparison from \(S(m)\), is
\[
                         (1+\mu(a))\log p\ge0 .
\]
If \(a\le R<pa\), only \(pa\) is admitted
and the contribution is
\((1-\mu(a))\log(m/a)\ge0\).
If \(pa\le R\), there is no contribution.
These cases include equality at each strict cutoff
and prove the exact one-small-prime statement.

For a prime \(y\), all raw and free terms have \(\log s=0\).
For a squarefree semiprime the only nonzero raw \(r\) can
be a single prime above \(R\); \(c=1,a=r\) then exactly
cancels it, while \(c=r\) cannot have \(a>R\).
This proves the lower-rank assertions.

## 3. Actual negative mass with two tiny factors

Fix \(0<\epsilon\le10^{-3}\). Take genuine distinct primes
with \(y=pq B g\) in the following open ranges of \(\log_x\):
\[
 p\in(.55\epsilon,.60\epsilon),\quad
 q\in(.66\epsilon,.70\epsilon),\quad
 g\in(.54,.56),\qquad
 B=\frac{y}{pqg}\ \text{of exponent in }(.43,.47).
                                                                    \tag{4}
\]
Here the displayed intervals mean logarithmic exponents,
not the primes themselves. Take \(y\in[1.24x,1.27x]\).
For sufficiently large \(x\) all these primes exceed \(z\);
the only \(c<C_y\) divisors are exactly \(1,p,q\).
In particular their product \(pq\) fails the moving strict cutoff
because its exponent exceeds \(1.21\epsilon\).
The giant \(g>R\) is required in every admitted divisor
\(a\), because \(y/g<R\).
Writing \(m=pqB\), one gets
\(K(y)=-\Lambda(m)=0\).
Also \(S(y)=4\log m\), \(S(y/p)=2\log(m/p)\)
and \(S(y/q)=2\log(m/q)\).
Equation (3) therefore yields the exact **negative** weight
\[
                         R_\epsilon(y)=-4\log B.                  \tag{5}
\]
This is a negative whole physical value, not a selected
negative summand that an opposing summand at the same \(y\)
could reverse.

To see actual mass at every target, restrict the true slope
to \(e\in[.70Y,.71Y]\), so every \(y\) in the fixed window
has its reconstructed \(k=(N-y)/e\in[Y,1.1Y]\).
Open the **slope** modulus \(e\) and sum these physical \(k\)'s.
Use [Fouvry, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
on fine independent boxes with the true shortest prime \(p\)
as the short Siegel–Walfisz slot and the other three genuine
primes as the independent grouped coefficient.
The residue is the fixed actual \(N\), the modulus \(e\asymp x^{1/2}\)
is below both ranges \(x^{1/2+\log_x p/2}\) and
\(x^{4/7-6\log_x p/7}\) by a fixed margin for the fixed
\(\epsilon\), and the theorem gives arbitrary-log precision
for bounded actual \(\beta(e)\).
Omit actual target-dividing primes inside the four slots,
which leaves the literal \((k,N)=1\) condition.
Smaller smooth boxes in (4) have the same lower mass order.
The modulus scale and box anchoring keep \(|N|\le4M_0N_0\)
with \(M_0,N_0\) the two source lower anchors.

The reduced principal follows by PNT in \(g\) and
reciprocal prime sums in the other three slots.
Both small exponent intervals carry reciprocal measure
bounded below independently of fixed \(\epsilon\), since
each is a fixed multiplicative interval in exponent.
The giant angle ranges over a fixed interval, and
\(\log B/L\) is bounded below.
Thus (5) gives mass \(\gg x/\varphi(e)\) in the model
on each fixed \(e\), independently of fixed \(\epsilon\).
Finally the actual slope-tag harmonic sum
\(\sum_{e\in[.70Y,.71Y],(e,N)=1}\beta(e)/\varphi(e)
 \gg\varphi(N)/N\) follows by counting the free cofactor of
each true tag pair and its positive reciprocal prime mass.
The arbitrary-log errors for fixed \(\epsilon\)
are smaller than this lower bound.
This is a true fixed-target total over the \(k\)'s, not
a per-\(k\) signed comparison to an opposite row.

## 4. Separate capped option on the same box

The above sign theorem is for the **uncapped**
hyperbolic threshold. Alternatively take
\(\widehat T_{\epsilon,\theta}(s)=\min(T_\epsilon(s),x^\theta)\)
with fixed \(\theta>.505\), for example \(\theta=.611\)
on the original two-tag box.
The difference in free scores is a one-free band
\(x^\theta<a\le T_\epsilon(s)\).
When activated, \(s T_\epsilon(s)=x^{1-\epsilon}\),
so both harmonic \(c\)-endpoints are
at least \(y/x^{1-\epsilon}\ge x^\epsilon\).
The elementary floor proof in the
[flat cap lemma](../flat_cap_composite_proxy/Proof.md)
therefore gives arbitrary-log cancellation for
\(Q\le x^{\theta-\delta}\).
The capped proxy still transfers on the original box
and exactly kills all integers with a true prime \(>x^\theta\).

For this capped alternative, rank four without a giant \(>R\)
is nonnegative by the floor pairing in the endpoint proof.
For a genuine \(R<g\le x^\theta\), every accepted
free divisor contains \(g\), and the directed singleton
charge \(i\to j\) may be unpaid only when
\(\widehat T_{\epsilon,\theta}(p_i p_j)<g\).
In that case \(T_\epsilon(p_i p_j)<g\) too, because
the cap \(x^\theta\) is at least \(g\),
including at equality \(g=x^\theta\).
It follows that \(g p_i p_j>x^{1-\epsilon}\),
so the remaining small prime is
\[
                        y/(g p_i p_j)< C_y .
\]
This proves a **one**-small-factor necessary condition
for negative rank four in the capped alternative.
It is not the uncapped **two**-small-factor theorem
for arbitrary ranks; combining the caps does not
license that stronger sign statement.
The actual small-prime covariance remains open in both versions.

