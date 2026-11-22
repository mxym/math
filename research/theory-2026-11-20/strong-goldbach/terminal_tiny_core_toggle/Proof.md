# Exact same-row payment of the terminal tiny-core giant debit

Use the actual [all-small completed score](../completed_gap_two_true_sectors/Proof.md),
not the fixed-payer score. Let \(N=2x\) be even, \(L=\log x\),
\(\ell=\log L\), \(z=x^\chi\) with \(\ell^{-2}\le\chi\le\ell^{-1}\),
\(J=xJ_0\subset[x,1.5x]\), and \(P=N-y\) an actual prime.
All the \(y\)'s in this note are \(z\)-rough and squarefree, and
\(T_y=\log y/(2L)\).
Fix \(0<\epsilon<.005\), so that \(C_y=y/x^{1-\epsilon}\)
is the actual cutoff for the small factors.
For sufficiently large x put
\[
 K=M=\left\lceil100\,\frac{\log\log\ell}{\log\log\log\ell}\right\rceil,
 \qquad U=100\chi\log\ell,\qquad R_\pm(y)=\sqrt y\,x^{\pm U}.
\]
These choices also fit the parameter uniformity of the
[collective tiny-core compensation](../prime_short_core_compensation/Proof.md):
\(K E_M=o(1)\), \(K^2U^2=o(1)\), and \(\rho(K)\log\ell=o(1)\).
Here we use only its actual d-support, not its sign budget.

A short actual divisor \(d<\sqrt y\) has depth
\(t_d=T_y-\log d/L\). A pair \(\{d,v=y/d\}\) with
\(0<t_d<U\) lies entirely in the central raw-only part of
the **actual** gap score: both divisors exceed \(R_-(y)\),
neither exceeds \(R_+(y)\), and the completed free sum has
no term belonging to this pair. Its exact contribution is
\[
       C(y,d)=\mu(d)\log v+\mu(v)\log d
         =\begin{cases}
             \mu(d)\log y,&\mu(y)=+1,\\
             2\mu(d)t_d L,&\mu(y)=-1.
           \end{cases}                                         \tag{1}
\]
In particular this is not the gap-minus-own-root bracket.

Let \(\mathcal T\) be the actual central pairs with
\(0<t_d<M\chi\) and \(d=pA\), \(p\) a genuine prime and
\(1\le A\le z^K\). The p necessarily exceeds \(x^{.49}\)
eventually, and is unique in d. No restriction is placed on
how many actual prime factors, of either size, occur in v.

**Theorem.** Except for an \(o(x\mathfrak S(N))\) total absolute
negative cost after weighting by the genuine \(\log P\), every
negative \(C(y,d)\) in \(\mathcal T\) has a distinct actual
positive receiver pair on the same physical y in the same
gap score, with opposite value. The receiver is at depth
\(>2M\chi\) and \(<U\). Its short divisor has a prime factor
in
\[
               \mathcal B=(z^{3K},\,z^{50\log\ell}]\cap\{\text{primes}\}
                                                                  \tag{2}
\]
and hence cannot have the form \(p'A'\) with a near-root giant
\(p'\) and \(A'\le z^K\). It also cannot have all its prime
factors \(\ge x^{\vartheta}\) for any \(\vartheta\) with
\(\vartheta>50\chi\log\ell\). In particular the receiver excludes
the polynomial-minimum and the \(\vartheta=\ell^{-1/4}\) safe
receiver sets. The error is uniform in even N and in \(\chi\) in
the indicated range. It does not assert a small signed total
on the remaining exterior raw or safe orientations. If an
independent argument estimates a larger signed sector including
these receivers, their positive values cannot also be counted
as independent credit against another sector.

## 1. Literal complement toggle and injection

When \(\mu(y)=+1\), suppose \(v\) contains at least two
distinct actual primes from \(\mathcal B\).
Every member of \(\mathcal B\) dividing y belongs to v:
\(p\) is much larger, and every prime in A is at most \(z^K\).
Choose the least \(\mathcal B\)-prime dividing y, call it r,
independently of the incoming d. Toggle r from v into d:
\[
         \{d,v\}\ \longmapsto\ \{dr,\ v/r\}.
\]
Since \(r\) is squarefree in y, the toggle is well-defined
on unordered complementary divisor pairs and is involutive:
complement commutes with changing one prime bit. Because
\(\log r/L>3K\chi\ge3M\chi\), the receiver short divisor is
\(b=v/r\), and
\[
        t_b=\log r/L-t_d\in(2M\chi,\ 50\chi\log\ell)\subset(0,U).
\]
Thus both sides of the new pair are still genuinely raw-only.
Their common Möbius sign is the negative of the incoming
common sign. Formula (1) gives the opposite value exactly.
The involution is injective at each y and every receiver
lies outside the terminal depth. The at-least-two condition
leaves another bank prime in b. That prime is larger than
\(z^K\) but has subpower size, so cannot be the possible
near-root giant of b. These two literal support properties
prove the disjointness assertions.

If \(\mu(y)=-1\), we do not use a receiver in this
narrow-giant theorem. Formula (1) already bounds the
debit by \(2M\chi L\) per pair. We now pay this and the
true at-most-one-bank exception on the even rows.

## 2. True rare-bank bound, not an independent prime model

For fixed actual A,p put \(d=pA\). The presence of the
short divisor in \(\mathcal T\) implies
\[
    x^{1/2-M\chi}<pA<\sqrt{1.5x},
        \qquad   \sum_{p:\ \mathrm{eligible}}\frac1p
                          \ll M\chi+L^{-1}.
\]
The latter follows from ordinary prime Mertens or prime dyads,
since \(p\ge x^{.49}\). The true core harmonic sum is
\(\sum_{A\le z^K,P^-(A)>z}\mu^2(A)/A\ll K\) by its upper
Euler product (including \(A=1\)). Opposite primes dividing
N account for only \(O(1)\) possible physical y, with
\(x^{o(1)}\) total cost from divisor and log weights. Otherwise
\((d,N)=1\). We may drop squarefreeness for the upper estimates.

We need a true count for \(v\in[x/d,1.5x/d]\) with
\(P=N-dv\) prime and \(v\) \(z\)-rough. For any fixed
sub-bank \(\mathcal Q\subseteq\mathcal B\), add the requirement
that v avoid \(\mathcal Q\). An ordinary two-form upper
Selberg sieve gives, uniformly in the actual sub-bank,
\[
 \#\{v:\ P\ {\rm prime},\ P^-(v)>z,\ (v,\textstyle\prod_{r\in\mathcal Q}r)=1\}
 \ll \frac{x\mathfrak S(N)}{d\,\chi L^2}
                      \prod_{r\in\mathcal Q}(1-1/r).             \tag{3}
\]
Indeed sieve \(P\) up to \(x^{.01}\), and sieve v additionally
at the primes \(\le z\) and at \(\mathcal Q\).
The bank (2) lies below \(x^{.01}\) eventually, uniformly
in \(\chi\). At primes not dividing \(dN\) there is one root
when sieving just P and two distinct roots when also sieving v.
At primes dividing N the roots coincide, including at 2;
at primes dividing d the P-form is a nonzero constant.
The usual local product is at most a fixed multiple of
\(\mathfrak S(N)V_z/L\) times the additional bank product.
Indeed the primes dividing d are \(>z\) and their local
correction costs \(1+O(L/z)\). Extra collisions on the optional
bank at \(r\mid N\) cost \(1+O(L/z)\) as well; at small
\(r\le z\), the collisions give exactly the truncated Goldbach
singular series relative to the two independent Mertens products.
For comparison at ordinary r, the ratio between \(1-2/r\) and
\((1-1/r)^2\) is \(1+O(r^{-2})\).
We used \(V_z\asymp1/(\chi L)\).
The dimension is at most two uniformly. For example take
Selberg divisor level \(x^{.10}\); its squared expansion
uses floor errors totaling \(O(x^{.20}L^{O(1)})\) with
bounded divisor coefficient orders, negligible in the
free interval of length \(\asymp x/d\gg\sqrt x\).
The fixed ratio between level and maximal sieve-prime size
is more than enough for the standard bounded dimension-two
upper factor. The genuine \(P\ge x/2\) exceeds that maximal
sieve prime. These estimates, including the floor reserve,
are independent of which set \(\mathcal Q\) is chosen.

For the at-most-one-bank event, choose each prime of
\(\mathcal B\) in \(\mathcal Q\) independently with probability
\(1/2\), just as a finite averaging device. For every physical v
the chance that it avoids \(\mathcal Q\) is exactly
\(2^{-\omega_{\mathcal B}(v)}\). The indicator of at most
one bank factor is bounded by \(2\cdot 2^{-\omega_{\mathcal B}(v)}\).
Averaging the true upper (3), not a conditional prime hypothesis,
therefore gives an upper with extra factor
\[
  \ll \prod_{r\in\mathcal B}(1-1/(2r))
  \ll \left(\frac{K}{\log\ell}\right)^{1/2}.                     \tag{4}
\]
The last step is genuine prime Mertens at the displayed actual
endpoints: \(\sum_{r\in\mathcal B}1/r
=\log((50\log\ell)/(3K))+o(1)\). In particular no number of
required bank primes is lost at a target prime divisor; the
local correction was included before averaging.

Use (3) with empty \(\mathcal Q\) for the odd y's and with (4)
for the deficient even y's. The first cost, after multiplying
by actual \(\log P\) and \(2M\chi L\), is
\[
                   \ll x\mathfrak S(N) M^2K\chi=o(x\mathfrak S(N)).
\]
The second, using \(\log y\), is
\[
       \ll x\mathfrak S(N) MK
                    \left(\frac K{\log\ell}\right)^{1/2}
                   =o(x\mathfrak S(N)).
\]
For example \(\log M+\log K=O(\log\log\log\ell)\)
while \(\tfrac12\log\log\ell\) in the denominator of (4)
dominates. The \(L^{-1}\) boundary loss in the p harmonic
is smaller. This proves the theorem on the full physical
tiny-core family, including cases with no macro prime at
all in the long partner v.

All credited scores are the literal same-row raw terms.
The result neither counts any new prime pair nor treats the
known signed shoulder evaluations of other sectors as unused
credit automatically.

A [separate wider-gap theorem](../wide_gap_all_terminal/Proof.md) removes the tiny-core hypothesis from the terminal packet and treats both total parities by exact raw-only orbits. It verifies the new score's calibration but not the signed remainder outside the selected orbits.
