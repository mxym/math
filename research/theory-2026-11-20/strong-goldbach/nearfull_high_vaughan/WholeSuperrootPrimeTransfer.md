# Transfer of one full super-root mark orientation to a genuine prime opponent

Let \(N\) be an individual large even target, \(J\Subset(0,1)\)
a fixed interval of positive length, \(x\in NJ\), \(y=N-x\),
\(L=\log N\), and \(M_N=|J|N\mathfrak S(N)\).
Write \(\Pi(y)=1_{y\ {\rm prime}}\log y\).
All sums below over \(x\) retain \((x,N)=1\).
For a fixed smooth profile \(H\) on \([0,\infty)\), put
\[
 t_d(z)=\frac{\log(dN/z)}{L},\qquad
 Q_H(m;z)=\sum_{d\mid m}\mu(d)H(t_d(z)).
\]
On the right let \(G\) be real and smooth, supported in \([0,b]\),
with \(U=N^\lambda\), \(b,\lambda>0\), \(b+\lambda<1/2\).
Its full genuine composite score is
\[
 P_G(y)=\sum_{\substack{q\mid y,\ q\ {\rm prime}\\U<q<y}}
                  (\log q)Q_G(y/q;y),
 \qquad a_G=G(0)-(1-\lambda)G'(0).
\]
Choose any fixed \(\rho>1/2\) with \(\rho+\lambda>1\).
If \(F\) is any fixed compactly supported smooth real profile
on \([0,\infty)\) and \(\mathcal R\subset(N^\rho,N]\) an interval
with arbitrary endpoints, define the physical sector
\[
 B_F(x)=\sum_{\substack{r\mid x,\ r\ {\rm prime}\\r\in\mathcal R,\ r<x}}
                 (\log r)Q_F(x/r;x).
\]
One may intersect \(\mathcal R\) with an additional original
lower mark gate. The prime \(r\) is unique when it occurs,
and \(x/r>1\) is required throughout.

**Theorem.** Uniformly in the actual endpoints of \(\mathcal R\),
at every large even \(N\),
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)P_G(y)
  =a_G\mathfrak S(N)\sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)
     -G(0)\sum_{\substack{x\in NJ\\(x,N)=1}}B_F(x)\Pi(y)
     +o_{F,G,J,\rho,\lambda}(M_N).                              \tag{1}
\]
No radical condition is imposed. This treats the **whole**
literal left super-root orientation, including unbounded ranks
and all prime powers in both cofactors. For example,
\((\rho,\lambda,b)=(.510,.498,.001)\) is allowed.
If \(a_G=0\), the paired sector is just the negative
of the one-leg true-prime correlation, times \(G(0)\).
That remaining correlation is not evaluated by this theorem.

This is different from
[the both-mark block](JointGiantActualMarkBlock.md)
and [the asymmetric both-mark transfer](AsymmetricGiantMarkDispersion.md):
the right mark stays completely unopened until a short-divisor
identity replaces its entire score, not a selected right window.
It uses the endpoint coefficient from
[the joint derivative formula](JointGiantEndpointDerivative.md).

## 1. Weighted distribution of a true long prime times a short integer

Fix \(\eta>0\), restrict temporarily to \(P^-(m)>N^\eta\), and
allow any signed \(\beta(m)\) bounded by a fixed power of
\(\tau(m)\), supported on this restriction and on \(m>1\).
Let \(\alpha(r)=(\log r)1_{r\in\mathcal R,\ r\ {\rm prime},\ (r,N)=1}\).
A bounded smooth factor of \(\log r/L\) is allowed in \(\alpha\)
if its derivative is bounded on \([\rho,1]\).
Place \(1_{(m,N)=1}\) in \(\beta\). We prove true product
Bombieri--Vinogradov for \(\alpha(r)\beta(m)\) at
\(q\le Q=N^{\lambda+b}\), \((q,N)=1\), with any fixed
\(\tau(q)^C\) weighting, for the actual reduced residue \(N\).
The principal is the same sum restricted to \((rm,q)=1\)
and divided by \(\varphi(q)\). No distribution assumption is
made on \(\beta\).

First work on dyads \(r\asymp R,\ m\asymp B\) that meet the
central product support; \(RB\asymp_J N\),
\(R\gg N^\rho,\ B\gg N^\eta,\ R\ll N^{1-\eta}\).
For a separable Mellin phase \(r^{it}m^{it}\), with any fixed
\(|t|\le L^T\), use characters modulo \(q\). A nonprincipal
character is induced by a primitive nonprincipal \(\chi\bmod k\),
\(k\mid q\), \(k>1\). The \(r\)-slot is already a unit since
\(r>Q\). To restore the imprimitive condition in the \(m\)-slot,
use \(\sum_{g\mid(m,q)}\mu(g)\), put \(m=gw\), and discard
\((g,k)>1\) where the primitive character vanishes.
Then \(kg\mid q\). There is no term with \(g\) longer than the
\(m\)-interval. Grouping over all such true moduli gives
\[
 \sum_{\substack{q\le Q\\kg\mid q}}
       \frac{\tau(q)^C}{\varphi(q)}
 \ll_C \frac{\tau(k)^C\tau(g)^C}{\varphi(k)\varphi(g)}L^{O_C(1)} .
\]
Here submultiplicativity of \(\tau\), supermultiplicativity
of \(\varphi\), and its divisor-weighted harmonic suffice.
This is a bound for the weighted absolute discrepancy itself.

For \(k\le L^{D_0}\), genuine prime Siegel--Walfisz in the long
slot, with partial summation for the Mellin phase and any
allowed angular factor of \(r\), gives \(O_A(RL^{-A})\).
Removing actual prime divisors of \(N\) in this slot costs
only \(O(L^2)\). Sum the short sequence trivially and take
the Siegel--Walfisz accuracy after \(D_0,T,C\).
For \(k\asymp K>L^{D_0}\) use the multiplicative large sieve
and Cauchy. The two squared sequence norms are at most
\(R L^{O(1)}\) and \((B/g)\tau(g)^{O(1)}L^{O(1)}\);
if the shortened interval has length comparable to 1 the
latter remains valid with an absolute factor. The resulting
bound, before the \(g\)-weight and fixed log losses, is
\[
 \frac{K^\epsilon\sqrt{N/g}}K
      \sqrt{(R+K^2)(B/g+K^2)}
 \ll K^\epsilon\left\{
       \frac{N}{gK}+\sqrt{NR/g}+\frac{\sqrt{NB}}g
                            +K\sqrt{N/g}\right\}.               \tag{2}
\]
The loss \(K^\epsilon\) absorbs \(\tau(k)^C\), with
\(\epsilon>0\) fixed arbitrarily small after all power margins.
The factors \(K^{-1}\), \(R+K^2\), \(B/g+K^2\) follow
directly from the weight \(k/\varphi(k)\) of the primitive
large sieve. The \(g\)-sum converges absolutely using
\(\tau(g)^{O(1)}/(\varphi(g)\sqrt g)\).
All but the first term of (2) save fixed powers, because
\(R\ll N^{1-\eta}\), \(B\ll N^{1-\rho}\) and
\(K\le Q/g\le N^{\lambda+b}<N^{1/2}\).
Take \(D_0\) large for the first. The resulting error is
\(O_A(NL^{-A})\) after any fixed log powers of dyads.

Here is a spatial version sufficient for all the products below.
Replace \(1_{x\in NJ}\) first by a smooth spatial cutoff on
\(x/N\) whose transition strips have length \(O_J(L^{-D_1})\).
Inserting any fixed \(G(t_d(y))\), \(\log(y/d)\), and
\(e^{i\xi\log(N/x)/L}\) with \(|\xi|\le L\) gives a test
in \(x/N\) on a fixed compact subinterval of \((0,1)\) with
log-power seminorms, uniformly in the literal \(d\) and \(\xi\).
Its Mellin transform on the imaginary axis is bounded by
a common integrable majorant with log-power norm, and its
\(|t|>L^T\) tail has arbitrary log savings after \(T\) is chosen.
The same holds for a sum of such tests at one \(q\) with the
fixed divisor multiplicity already included in \(\tau(q)^C\).
The true congruence sum taken absolutely over \(q\) in the
Mellin tail is \(NL^{O(1)}\): the actual \(q\) divides \(N-rm\),
so at any fixed physical \(x=rm\) the total weight is bounded
by \(L^{O(1)}\tau(x)^{O(1)}\tau(N-x)^{O(1)}\).
The absolute reduced principal is also \(NL^{O(1)}\)
by the \(1/\varphi(q)\) harmonic. These estimates are on
the central dyad range \(x\asymp_J N\); to use them for
Mellin inversion without support choose the product dyads
as subdivisions of fixed small ratio depending on \(J\).
Then all their products meeting the spatial support range
stay in a fixed compact subinterval of \((0,N)\), in
particular \(N-rm\ne0\). Consequently Mellin truncation
does not multiply its error by a power number of moduli.
The same true divisor envelopes and Cauchy on the two transition
strips give \(O(NL^{-A})\) after \(D_1\) is chosen, since
ordinary shifted divisor moments after Cauchy cost fixed log
powers. For the principal remove the strips using the
absolute \(1/\varphi(q)\) harmonic and the analogous one-leg
divisor moments. This restores the exact fixed interval
\(NJ\) and its literal weights; no assertion about arbitrary
simultaneous moving prefixes is needed.

## 2. Transfer with a polynomial least factor on the left

The exact short model on the right is
\[
 A_G(y)=\sum_{d\mid y}\mu(d)G(t_d(y))
    \left\{\log(y/d)-
        \sum_{\substack{k\mid y/d\\k\le U}}\Lambda(k)\right\}.
\]
By the prime-power identity,
\(P_G=A_G-G(t_1(y))\Pi(y)\), apart from proper-power marks
\(p^j>U,\ j\ge2\). The latter occur at
\(O(N^{1-\lambda/2+o(1)})\) physical integers and contribute
power-small in each pairing here, since all row weights
are bounded by fixed divisor powers times \(L^{O(1)}\).
The moduli of the exact \(A_G\) expansion are \(d\) and \(dk\);
there are no imposed unit conditions between \(d\) and its own \(k\).

Apply §1 to each genuine source described there, with
the optional bounded spatial phase and log factors.
On the principal, at a fixed \(x=rm\) all prime factors of \(x\)
exceed \(N^{\min(\eta,\rho)}\). The loss on removing
\((x,d k)=1\) while still retaining the target-unit conditions
is \(O(N^{-\min(\eta,\rho)}L^{O(1)})\) per source weight.
Indeed, for every actual \(p\mid x\), the portion of the
\(1/\varphi(d)\)-harmonic with \(p\mid d\) has a factor
\(O(L/(p-1))\); if \(p\mid k\), the full prime-power
\(\Lambda(k)/\varphi(k)\)-mass is \(O((\log p)/(p-1))\).
Use \(1/\varphi(dk)\le1/(\varphi(d)\varphi(k))\);
all other absolute harmonics cost fixed log powers.
The mask is removed only in the model, not in the true rows.

It remains to evaluate, uniformly in real central \(y\),
\[
 \sum_{(d,N)=1}\frac{\mu(d)}{\varphi(d)}G(t_d(y))
   \left\{\log(y/d)-
           \sum_{\substack{k\le U\\(k,N)=1}}
                   \Lambda(k)\frac{\varphi(d)}{\varphi(dk)}\right\}
   =a_G\mathfrak S(N)+o(\mathfrak S(N)).                        \tag{3}
\]
This is the pointwise finite endpoint calibration of
[ZeroCutoffExponentialMoment, §§1--2](ZeroCutoffExponentialMoment.md).
For the exact value \(U=N^\lambda\), one may also compute
it directly. Truncate the signed \(d\)-harmonic at
\(S=\exp((\log L)^4)\) through the uniform masked Möbius
tail, separately for each \(k\); its factors at primes of
\(Nk\) are allowed, and the other absolute harmonics cost
fixed log powers. Taylor expand \(G(t_d)\) on this box.
The absolute remainder is \(O((1+\log S)^3/L)=o(1)\)
after the \(O(L)\) bracket. For the constant and first-log
moments use
\(\sum_{(d,N)=1}\mu(d)/\varphi(d)=0\) and
\(\sum_{(d,N)=1}\mu(d)\log d/\varphi(d)=-\mathfrak S(N)\)
at the same cutoff up to arbitrary log errors.
The short-prime bracket differs from
\(\sum_{k\le U,(k,N)=1}\Lambda(k)/\varphi(k)
 =\lambda L+O(\log L)\)
by a sum over \(p\mid d\) with coefficients bounded by
\(\sum_{j\ge1}\log p/(p^j(p-1))\).
Against the constant Taylor term this difference is
arbitrarily log-small: for \(p\le\sqrt S\) replace \(d\)
by \(p d'\), using the masked zeroth moment with
\((d',Np)=1,\ d'\le S/p\). For \(p>\sqrt S\) the absolutely
summable coefficients give the bound. Against the first
Taylor term its absolute cost is \(O((1+\log S)^2/L)\).
Now the constant \(G(0)\) meets the term \(-\log d\),
and \(G'(0)\) meets \((1-\lambda)(\log d+\log(N/y))\);
the zeroth moment kills the spatial constant. This proves
(3) with the asserted signs.

The absolute source weight is \(O_\eta(N)\):
its rank with multiplicity is bounded on the rough support,
and
\(\sum_{m\le N,\ P^-(m)>N^\eta}|\beta(m)|/m=O_\eta(1)\)
by the prime reciprocal harmonic and bounded-rank Euler
expansion. For each fixed \(m\), genuine Chebyshev along
the \(r\)-interval gives weight \(O(N/m)\);
a bounded spatial factor does not change this estimate.
Thus the \(o(\mathfrak S(N))\) in (3) costs \(o_\eta(M_N)\).
For the genuine prime term the same harmonic bound and
the dimension-two affine prime upper for \(r,N-mr\)
give \(\sum|B(x)|\Pi(y)\ll_\eta M_N\); the length of the
true \(r\)-interval may be enlarged to the central full
interval at fixed \(m\ge1\), of length \(\asymp_J N/m\).
The local factor is \(\ll\mathfrak S(N)c(m)\), where
\(c(m)=\prod_{p>2,\ p\mid m}(p-1)/(p-2)\);
the extra \(c(m)\) does not affect the harmonic bound.
Consequently \(G(t_1(y))=G(0)+O(1/L)\) can be replaced
on this **true prime** pairing. This proves (1) for
the temporarily rough source, including any such \(\beta\).

For the desired rough \(B_F\) write, using a smooth compact
extension of \(F\) to the real line,
\[
 Q_F(m;x)=\frac{1}{2\pi}\int_\mathbb R
  \widehat F(\xi)e^{i\xi\log(N/x)/L}
                   \sum_{d\mid m}\mu(d)d^{i\xi/L}\,d\xi .
\]
Here the inner coefficient is uniformly divisor-bounded.
On \(|\xi|\le L\) the actual spatial factors are allowed
in §1; the Schwartz tail is arbitrarily log-small against
the true divisor envelopes and reduced principal.
This gives (1) on the rough \(B_F\) itself.

## 3. The full source: remove the polynomial rough floor at true scale

For each fixed \(m,n\), write \(x=mr,\ y=nq\) with the
two actual prime marks. On actual target units
\((m,n)=(mn,N)=1\). The two competing prime arguments
lie in primitive affine forms in an integer parameter
of length \(\ll_J N/(mn)\); enlarge to the full central
interval at fixed \(m,n\).
Here \(m\ll N^{1-\rho}\), \(n\ll N^{1-\lambda}\), so even
after enlargement the parameter length has a fixed power
scale \(N^{\rho+\lambda-1}\) or greater.
The two affine slopes are \(n,-m\). At a prime dividing
\(mn\) one form is a nonzero constant and the other gives
one root; at a prime dividing \(N\) the two roots coincide;
elsewhere there are two roots. This includes \(p=2\) with
one root, as \(N\) is even and both coefficients are units.
Apply the ordinary positive Selberg upper sieve to these
two forms at a small fixed power of the parameter length.
The primes \(r>N^\rho\) and \(q>N^\lambda\) themselves
exceed the sieve ceiling (shrink that fixed power if needed).
The two true log weights are \(O(L^2)\), canceling
the sieve denominator. The resulting bound at fixed \(m,n\)
is \(\ll_{\rho,\lambda,J} M_N c(m)c(n)/(mn)\).
This is the long-parameter branch of
[the true two-leg envelope](JointGiantFiniteRank.md);
it also follows by the elementary Selberg square in
[the polynomial reduction, §2](PolynomialSmoothedGiantReduction.md).
No distribution on moduli near \(mn\) is being invoked.

For a real \(\xi\) define
\(V_\xi(m)=\prod_{p\mid m}|1-e^{i\xi\log p/L}|\);
this product is valid with any multiplicities in \(m\).
The positive Euler harmonic
\[
 \sum_{m\le N}\frac{c(m)V_\xi(m)}m
     \ll (2+|\xi|)^C
\]
is uniform in \(\xi\) and \(N\). Expand the Euler product,
using a local prime-power sum \(1/(p-1)\); split at
\(\log p=L/(1+|\xi|)\), using
\(|1-e^{iv}|\le\min(2,|v|)\) and Mertens. If the split
is below the first prime, \(\log L\ll\log(2+|\xi|)\)
already bounds the exponent. With \(P^-(m)\le N^\eta\)
one can mark any such true prime and obtain an extra
\(O(\eta|\xi|)\) using \(\sum_{p\le N^\eta}\log p/p\ll\eta L\)
(the expression is zero if that interval is empty).
With the two integrable Schwartz weights this proves
that all genuine paired rows with such an \(m\) have
absolute weight \(O_{F,G,\rho,\lambda,J}(\eta M_N)\).
For the one-leg true prime opponent use the same bound
with \(n=1\). For the unconditioned source use genuine
Chebyshev at fixed \(m\), giving \(O_F(\eta N)\), and likewise
a bound \(O_F(N)\) on the entire source. These hypotheses
do not impose squarefreeness. The factor correction at
\(p=2\) is already in \(\mathfrak S(N)\), so including
even \(m,n\) in the nonnegative harmonic is harmless.
For each fixed \(\eta>0\) first take \(N\to\infty\) in
the rough transfer; then take \(\eta\downarrow0\) in these
absolute bounds, whose constants are independent of \(\eta\).
This proves the full \(o(M_N)\) in (1).

## 4. A genuine positive anchored sector under no binary pair

Take \(J\subset[1/2,2/3]\) as above, and select actual
squarefree \(x=ur\), where \(u,r\) are genuine distinct primes,
\[
          (N/2)^{.252}<u\le N^{.489},\qquad r=x/u.
\]
The right profile has \((\lambda,b)=(.498,.001)\);
choose \(G(0)=1,\ G'(0)=1/(1-\lambda)\), so \(a_G=0\).
Let \(F(0)=1\) flat near zero, \(F=4\) on \([.251,.490]\),
and take its support in \([0,.492]\) and its original
lower mark gate \(N^{.006}\).
These fixed smooth profiles exist and have
\(.006+.492<1/2\) for the full correlation.
Here \(r\gg_J N^{.511}>N^{.510}\), \(r>u\), and both marks
exceed the lower \(F\)-gate. The true spatial shifts
in \(t_1,t_u,t_r\) are \(O_J(1/L)\), so for all large \(N\)
the marked \(r\)-score is exactly \(-3\log r\),
and the whole \(F\)-score on these selected \(x\)'s is
\(-3\log r+\log u\). In the latter score the smaller
mark really contributes; it is not silently removed.

Let \(D\) be the actual \(\sum(\log x)\Pi(y)\) on these selected
\(x\)'s. Equation (5) and its certified numerical margin
in [the central rough trim](../least_factor_trim_2685/Proof.md)
give \(R_J(N)+D_2(.252)>.3001 M_N\), in exactly this
central normalization (\(J_0=2J\) in that proof).
By [the actual 3.446 angular bound](../angular_prime_first_composite/Proof.md),
the discarded semis with smaller factor \(>N^{.489}\)
weigh at most
\[
 \left(3.446\int_{.489}^{.5}\frac{du}{u(1-u)}+o(1)\right)M_N
       <(.152+o(1))M_N .
\]
Indeed \(3.446\log(511/489)<.152\), even with the rational
upper \(t-t^2/2+t^3/3\) for \(\log(1+t)\), \(t=22/489\).
The actual own-log angle versus \(\log N\) differs by
\(O_J(1/L)\), absorbed by the fixed Jordan collars in
that upper. Thus if \(R_J(N)=0\), then \(D>.148 M_N\)
for all large \(N\). All unit exceptions on the genuine
\(y\)-prime side have only boundedly many rows.

Use §2 directly with the actual prime \(u\)-mask.
It prices the selected \(-3\log r\) source against \(P_G\)
by the positive true \(\sum 3\log r\,\Pi(y)+o(M_N)\).
It also prices the \(\log u\) source: put
\(\beta(u)=1_{u\ {\rm prime}}(\log u)/L\) with the literal
interval, and insert the bounded smooth factor \(L/\log r\)
in \(\alpha\). The transfer then gives the exact
negative true \(-\sum(\log u)\Pi(y)+o(M_N)\).
Since \(\log u/\log x\le .4891\) eventually, under
\(R_J(N)=0\) the selected left \(r\)-marked cross exceeds
\(.22 M_N\), and the selected left **both-mark** cross
exceeds \(.15 M_N\). No restriction has been added
to the right genuine mark. These numerical reserves
are conditional positive sectors of the same physical product,
not lower bounds for the whole covariance. For these
\(F,G\), the full joint derivative formula is still
\(R_J(N)-M_N+o(M_N)\), since \(F'(0)=0\).
In particular substantial negative compensation elsewhere
would be necessary at a target with no binary representation;
the theorem does not control it.
