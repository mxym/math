# Odd-composite partners of a true near-half prime mark

Let \(J\Subset(0,1)\) be a fixed nondegenerate compact interval,
\(x\in NJ\), \(y=N-x\), and \(I=N(1-J)\). Write \(L=\log N\)
and \(\mathfrak S(N)\) for the binary singular series. Fix the
true mark range
\[
 \mathcal R=\{r\ {\rm prime}:N^{.4938}\le r\le N^{.4942},\
                                      (r,N)=1\},\qquad \Delta=.0004.
\]
Take a sufficiently small fixed \(\eta>0\), put \(z=N^\eta\),
and define the **positive actual source**
\[
 B(y)=\sum_{\substack{rm=y,\ r\in\mathcal R\\
         (m,N)=1,\ \mu^2(m)=1,\ P^-(m)>z}}\frac{\log r}{L},
 \quad y\in I,\qquad T=\sum_{y\in I}B(y).
\]
No primality requirement is put on the long variable \(m\).
The constants below are independent of the individual even \(N\).

**Theorem.** There are fixed \(\eta,\zeta>0\) and an integer \(K\)
such that, for every sufficiently large even \(N\), there are
\[
                 \gg_J\frac{N\mathfrak S(N)}{(\log N)^2}
\]
distinct actual pairs \(x+y=N\) with \(x\in NJ\), both \(x,y\)
squarefree target units, and the following features:
* \(x\) has an **odd** number of distinct prime factors, between
  3 and \(K\), and \(P^-(x)>N^\zeta\);
* \(y=rm\) for a genuine \(r\in\mathcal R\), with all actual
  prime factors of \(m\) exceeding \(N^\eta\).

In particular both summands have bounded rank, but no conclusion is
drawn that \(m\) is prime or that \(x\) has exactly three factors.
This is a true same-target parity statement with a prescribed prime
mark on the opposite leg, not a Goldbach representation.
The proof uses the fixed-target near-balanced distribution rails of
[the balanced genuine semiprime source](../balanced_semiprime_giant_cross/Proof.md),
with the long coefficient changed to the actual rough integer indicator.
The signed step and the even-rank debit are paid separately.
For comparison, the [conditional rough-parity result of Guo](https://github.com/aster2024/openai-math-followups#rough-goldbach-parity--sums-of-two-rough-numbers-with-prescribed-liouville-signs)
uses subpower roughness and a different two-sign test; we do not import its
analytic inputs.

## 1. Progression distribution for the actual changed source

For every fixed \(A>0\), this \(B\) satisfies
\[
 \sum_{\substack{q\le N^{.5055}\\(q,N)=1}}\sup_{I'\subset I}
 \left|\sum_{\substack{y\in I'\\y\equiv N\ (q)}}B(y)
      -\frac1{\varphi(q)}\sum_{\substack{y\in I'\\(y,q)=1}}B(y)\right|
                 \ll_{A,J,\eta}NL^{-A}.                          \tag{1}
\]
The supremum is over real intervals. Split \(r,m\) into fixed
log-fine boxes as in §1 of the cited semiprime-source proof. Their
scales \(M,Z_1\) satisfy \(MZ_1\asymp_J N\);
the long exponent is in \([.5058,.5062]+O(1/L)\).
Boundary strips at a product endpoint have total weighted count
\(O(NL^{-F})\) at log mesh \(L^{-F}\), by dropping all masks
and applying elementary integer counts, or just by noting that
each central product can have at most two such marks \(r\).
For the progression errors this is amplified by at most the
true shifted divisor envelope, and the reduced principal loses
only \(\sum_{q\le N}1/\varphi(q)\ll L\).
A log-fine additive prefix mesh gives the supremum in (1) using
the same bound for arbitrary endpoint strips, with the usual
summed \(+1\) floors. We may request any fixed log accuracy before
summing the meshes.

For the over-root and adjacent lower range
\(N^{.49355}\le q\le N^{.5055}\), use
[Fouvry–Radziwiłł, Theorem 1.1](https://arxiv.org/abs/1812.00562v2).
The strict rails are exactly those of the cited semiprime-source
proof: the lower extreme
\((56\cdot .5062-17)/23=.49335652\ldots<.49355\), and the
upper margin is at least \(.0003\). We use the same verified
fixed-factor extension of the residue bound to literal residue
\(N=O_J(MZ_1)\); no new range is needed.

Here the changed long coefficient is Siegel–Walfisz in the
precise sense of their Definition 1. Fix any reduced class
modulo a log-power \(q\) and arbitrary auxiliary unit mask \(A_0\).
Open the actual squarefree \(m\) into its largest prime \(p\)
and the product \(d\) of the others. All primes exceed \(N^\eta\)
and the rank is fixed-bounded. For each fixed \(d\), the true
\(p\)-interval is cut at the lower endpoints of the box, its
largest-factor ordering, and \(N^\eta\). It has scale \(\gg N^\eta\)
if nonempty. If \((d,q)>1\), neither reduced count contains it.
Otherwise the prime class is the actual residue multiplied
by \(\overline d\bmod q\). Require \((d,N A_0)=1\) and
remove the prime divisors of \(N A_0\) from this final slot.
This costs \(O(L+\omega(A_0))\) primes per \(d\); there are
\(O(Z_1/N^\eta)\) choices of \(d\). Prime Siegel–Walfisz at the
actual interval endpoints then gives \(O_D(Z_1 L^{-D}
\tau_2(A_0))\), since summing \(1/d\) loses at most \(O(L)\).
For larger \(q\) the trivial integer count \(O(Z_1/q+1)\)
and reduced principal \(O(Z_1/\varphi(q))\) give the stated
log-power error on increasing the split. This argument works
for arbitrary subintervals of the current long box. The upper
sieve support and the target mask here do not assert the long
variable is prime.

For \(q\le N^{.49355}\) the genuine \(r\)-variable exceeds every
modulus, unlike the long rough coefficient. We give the required
imprimitive check. If a character modulo \(q\) has primitive
conductor \(k\), the short sum is the same as with its primitive
ancestor. For the long sum retain \((m,q)=1\) by opening \(g\mid q\),
then put \(m=g w\). Terms with \((g,k)>1\) are already zero.
For fixed \(g\), the weight on \(w\) is the actual long coefficient
at \(g w\), of absolute value at most one, in an interval of scale
\(Z_1/g\gg N^{.012+o(1)}\). The primitive class is independent of
\(q\) after this split. Grouping over \(kg\mid q\) costs at most
\(O(L)/(\varphi(k)\varphi(g))\). The principal \(k=1\) was
subtracted before the imprimitive expansion. For \(k\le L^{D_1}\)
use Siegel–Walfisz on the real short prime slot and the trivial
long sum \(O(Z_1/g)\); choose log accuracy after \(D_1\).
On each remaining conductor dyad \(K_1\le N^{.49355}/g\),
Cauchy and the multiplicative large sieve give, apart from
fixed log powers, with \(X_g=MZ_1/g\),
\[
 \frac{\sqrt{X_g}}{K_1}
          \sqrt{(M+K_1^2)(Z_1/g+K_1^2)}
 \ll \frac{X_g}{K_1}+\sqrt{MX_g}+\sqrt{(Z_1/g)X_g}
                           +K_1\sqrt{X_g}.
\]
All the resulting \(g\)-harmonics are convergent since they carry
\(1/\varphi(g)\) times at least \(g^{-1/2}\).
Only the first term needs the logarithmic conductor reserve,
and all the other terms save a fixed power. This proves (1)
on low moduli as well. Fixed divisor powers in \(q\) are allowed
by clipping and the trivial discrepancy \(O(NL^2/q)\), as in
the same baseline proof.

For later normalization put \(V(z)=\prod_{p\le z}(1-1/p)\).
An ordinary dimension-one fundamental lemma on the \(m\)-interval
at each \(r\), with integer CRT divisor support \(N^{.10}\), gives
\[
 (1-\epsilon_0)|I|\Delta V(z)
       \le T\le(1+\epsilon_0)|I|\Delta V(z)                       \tag{2}
\]
for any prescribed small fixed \(\epsilon_0>0\) by choosing \(\eta\)
small enough and then \(N\) large. The sieve ratio is \(.10/\eta\).
Integer floors are power-small at length \(N/r\). Removing squares
of primes \(>z\) costs \(O((N/r)/z)\) by counting all actual
multiples in the positive interval. Target primes \(>z\) cost
\(O_\eta((N/r)/z+1)\); smaller ones are already omitted by
roughness. Finally the true prime-log harmonic in \(r\) is
\(\sum_{r\in\mathcal R}\log r/(Lr)=\Delta+o(1)\).
In particular \(T\asymp_{J,\eta}N/L\).

## 2. Signed symmetric score on the squarefree real partner

Choose smooth \(C(t)\) on \([0,\infty)\), equal to one through
\(t=.498\), equal to zero at \(t\ge.502\), with
\(C(t)+C(1-t)=1\) on \([0,1]\).
Put \(H(t)=(1+t(1-t))C(t)\) there and zero past its support.
Then \(H(0)=1\), \(H'(0)=1\), and
\(H(t)+H(1-t)=1+t(1-t)\). At an actual integer \(x>1\) let
\[
                 Q_H(x)=\sum_{d\mid x}\mu(d)
                                   H(\log d/\log x).
\]
We claim
\[
 \sum_{x\in NJ}\mu^2(x) B(N-x)(\log x)Q_H(x)
                  =-T\mathfrak S(N)+o_{J,\eta}(T\mathfrak S(N)).
                                                                  \tag{3}
\]
Here \(B\) already makes \(x\) a target unit. To prove (3), open
\(\mu^2(x)=\sum_{a^2\mid x}\mu(a)\). Keep \(a\le N^{.001}\)
with no local sieve approximation. The actual contribution of
larger \(a\), bounded before any progression calculation, is
\(N^{.999+o(1)}\): count at most \(N/a^2\) positive multiples
for each and use \(B(y)\le2\) and the usual fixed divisor-power
envelope. Only \(d\le N^{.502}\) occurs. The true modulus is
\([a^2,d]\le N^{.504}\); it is a reduced class on the source
since \((x,N)=1\). Up to \(\tau(q)^2\) allocations at any modulus,
(1) and real partial summation apply, including the true
\(\log x\) argument and its central spatial interval. The
coefficient has supremum and variation \(O_H(L)\).

In the reduced principal one may drop \((y,[a^2,d])=1\) at
power saving. Every prime factor of \(y\) exceeds \(z\).
Write \(d=u d'\) with \(u\mid a,\ (d',aN)=1\) on the
squarefree \(d\)-weights. Then
\(\varphi([a^2,d])=\varphi(a^2)\varphi(d')\).
For a prime \(p\mid y\), the positive harmonic loss from \(p\mid a\)
is \(O(L/p^2)\) before the free log, using the convergent
\(\sum_a\tau(a)/\varphi(a^2)\); the loss from \(p\mid d'\)
is \(O(L/p)\). Sum over the bounded rank of \(y\).
This proves that dropping the restriction in the model is harmless
after multiplying by \(\log x\) and summing the source masses.

For fixed \(a,u\) in the resulting sum, the actual smooth harmonic is
\[
 (\log x)\!
   \sum_{(d',aN)=1}\frac{\mu(d')}{\varphi(d')}
        H\!\left(\frac{\log u+\log d'}{\log x}\right)
 =-\mathfrak S(aN)H'\!\left(\frac{\log u}{\log x}\right)+o(1)
                                                                  \tag{4}
\]
uniformly in those labels, with the \(H\) cutoff extended by zero.
Indeed the signed zeroth moment is zero and the negative first
log moment is \(\mathfrak S(aN)\), with uniform Mertens tails by
[the original reduction, §1](../giant_prime_divisor_remainder/Proof.md)
applied to target mask \(aN\le N^2\). For example Taylor at the
displayed origin for \(d'\le\exp(L^{1/4})\); the absolute
quadratic remainder after multiplication by \(\log x\) is
\(O(L^{-1/4})\), since \(\sum_{d'\le Y}(\log d')^2/\varphi(d')
\ll(1+\log Y)^3\). Beyond this length use the uniform signed
tail and partial summation. The bounds for the original proof's
Euler norm apply also at that length, with exponential savings
in \(L^{1/8}\) and in \(L^{1/4}/(10\log L)\).
After weighting (4) by \(\mu(u)\), the \(a>1\) terms
cancel at the constant \(H'(0)\) by \(\sum_{u\mid a}\mu(u)=0\).
Their remaining total at fixed \(x\) is \(O_H(\mathfrak S(N)/L)\):
use the Lipschitz bound \(O_H(\log a/L)\) and
\[
 \sum_a\frac{\tau(a)c(a)(1+\log a)}{\varphi(a^2)}<\infty,\qquad
 c(a)=\prod_{\substack{p\mid a\\p>2}}\frac{p-1}{p-2},
\]
for squarefree \(a\). The target-unit \(a\) are odd and
\(\mathfrak S(aN)=\mathfrak S(N)c(a)\) on them.
Thus only \(a=1\) contributes the leading
\(-H'(0)\mathfrak S(N)\). All physical errors in (1) and the
large-square restoration are \(o(T\mathfrak S(N))\) by (2).
This proves (3) with the exact squarefree mask, without
discarding tiny square factors from a signed source by fiat.

At a prime \(x\), \(Q_H(x)=1\).
For squarefree even rank, complement every subset to replace
\(H\) by half of \(1+t(1-t)\); it follows that
\[
 Q_H(x)=
 \begin{cases}
       -u(1-u),&x=pq,\ u=\log p/\log x,\\
       0,&\omega(x)\ {\rm even},\ \omega(x)\ge4 .
 \end{cases}                                                     \tag{5}
\]
The first line is the exact quadratic finite difference.
No sign is assumed on the still uncounted odd ranks.

## 3. A strict cap for the actual even-rank debit

Define
\[
 E_2=\sum_{\substack{x\in NJ,\ x=pq\ {\rm squarefree}\\p,q\ {\rm prime}}}
                   B(N-x)(\log x)\,u(1-u).
\]
We show \(E_2\le .7 T\mathfrak S(N)\) for the fixed choices.
First restrict both true primes \(p,q>N^\beta\), with \(\beta>0\)
fixed small, and then choose \(\eta<\beta\) still much smaller
than \(.004\). Open the actual \(r\mid y\) in \(B(y)\).
For an upper on \(P^-(y/r)>z\) use a dimension-one upper
fundamental-lemma sieve in \(y/r\), at divisor support
\(e\le N^{.004}\). Omit primes dividing \(N\): they cannot divide
the physical \(y\) on target units. We may discard \(\mu^2(y/r)\)
in this positive upper. The genuine progression on the
**true semiprime** \(x\) is \(x\equiv N\bmod r e\), reduced.
Its modulus is at most \(N^{.4982}\), and \(r>z\) so
\(r,e\) are coprime. Primes of \(e\) cannot actually divide
either \(p\) or \(q\), by the fixed angular floor \(\beta>\eta\).

We spell out the product-BV transfer for these moduli.
Write the weight \((\log x)u(1-u)=\log p\log q/\log x\);
both normalized prime weights are independent on log-fine
boxes, and the product factor is a smooth spatial weight.
The target-unit condition removes the prime divisors of \(N\)
separately on each genuine prime slot; this is harmless for
its Siegel--Walfisz estimate and for the large sieve.
Divide the ordered count by two and remove \(p=q\), whose
actual total after opening \(r,e\) is \(N^{1/2+o(1)}\) by
the fixed divisor-power bound on \(N-p^2\). Its model total
is also negligible by the ordinary absolute reciprocal-modulus
harmonic with divisor weights.
On each box the two true prime slots have lengths of
polynomial scale at least \(N^\beta\).
After subtraction of the reduced principal and grouping
imprimitive characters, the only possible missing prime
variable is the genuine prime \(r\) of \(r e\), as neither
slot shares the small \(e\)-alphabet. That term has conductor
\(k\mid e\) (otherwise it was already zero).
For an \(r\) pinned in one slot, use the trivial other-slot
length \(\ll N^{.5062+o(1)}\).
Summing \(\sum_{k\mid e}\varphi(k)=e\), then
\(\sum_{e\le N^{.004}}e/\varphi(e)\ll N^{.004}\) and
\(\sum_r1/\varphi(r)\ll1\), makes these corrections
\(O(N^{.5102+o(1)})\), even before arbitrary log-power
precision. This also pays the correction with both slots
pinned. On the remaining unrestricted primitive prime sums,
small conductors use Siegel–Walfisz and large ones use the
same two-slot large-sieve bound as §1 with \(g=1\),
\(K_1\le N^{.4982}\). In particular each slot has a fixed
power margin. This proves the absolute distribution sum
needed over actual \(r e\); the grouping multiplicity is
divisor-bounded. Log-fine product, endpoint, and spatial
weights are paid by divisor moments and the true actual
product supports as in §1. No distribution of arbitrary
rank-selected sources is assumed.

In the reduced model, ignoring the coprimality with \(r\)
changes only a power-small term, since existing
\(x\) with a factor \(r\) have their other factor
at scale \(N/r\). The exact conditional density of \(e\)
is then \(1/\varphi(e)\).
With \(V_N(z)=\prod_{p\le z,p\nmid N}(1-1/(p-1))\) the
fundamental lemma makes the upper Euler main at most
\((1+\epsilon_0)V_N(z)\).
Its ratio to \(V(z)\) is \((1+o(1))\mathfrak S(N)\),
uniformly in \(N\): compare each exact factor and use the
summable non-target \(p^{-2}\) tail and \(O(L/z)\) target tail.
The outer \(r\)-harmonic is \(\Delta+o(1)\), while the
ordinary positive true E2 source with the weight above has
mass at most \((1/2+o(1))|J|N\).
For the latter take \(p\le q\) and use PNT on \(q\in NJ/p\);
the weight after the \(\log q\) prime sum is
\((1+o(1))\log p/L\), with
\(\sum_{p\le \sqrt N}\log p/p\sim L/2\).
All asymptotic evaluations may first keep a fixed small
margin from the equal-factor boundary, and the removed edge
has vanishing positive mass by the true reciprocal harmonic.
An upper may ignore the target unit constraint there.
Together with (2) this prices the macroscopic-prime part by
at most \((1+\epsilon_0)/(2(1-\epsilon_0))+o(1)\)
times \(T\mathfrak S(N)\).

It remains to charge actual \(p\le N^\beta\), with
\(p\) the smaller factor. At each fixed \(p,r\) (distinct
target units), solve the exact equation \(p q+r m=N\)
as \(q=q_0+r k,\ m=m_0-pk\).
The real \(k\)-interval has length \(\asymp_J N/(pr)\)
and both forms are primitive. For \(m\) sift only primes
through \(z\), and for the actual prime \(q\) sift up to
\(N^{.0005}\). At small primes off \(Npr\) there are two
roots, at target primes one coincident root, at \(p\) at
most one, and at primes above \(z\) just the \(q\)-root
apart from the excluded leading coefficient prime. The
singular correction is \(O(\mathfrak S(N))\) uniformly.
The standard positive Selberg upper with support \(N^{.01}\)
and the floor check of [WholeGiantSmallFactor, §3](WholeGiantSmallFactor.md)
therefore gives
\[
 \ll_J \frac{N\mathfrak S(N)}{p r\,L\log z}
\]
actual pairs per \(p,r\); the length is at least
\(N^{.5058-\beta+o(1)}\).
Every true \(q\) exceeds the sifting range.
The weight \((\log x)u(1-u)\) is at most \(\log p\);
sum \((\log r)/(Lr)\) then
\(\sum_{p\le N^\beta}(\log p)/(Lp)\ll\beta\).
Since \(V(z)\asymp1/\log z\), the total tiny-factor debit is
\(O_J(\beta T\mathfrak S(N))\), with the constant uniform in
sufficiently small \(\eta,\beta\).
Choose \(\beta\) first to make this coefficient \(<.1\),
then \(\eta<\beta\) sufficiently small for both fundamental
lemmas with \(\epsilon_0=.02\). This proves the announced
\(.7\) cap. In contrast, the above switched rank-two debit
could not be priced this way if the long quotient \(m\)
of the source were required to be prime.

## 4. The surviving true odd rows and their absolute tails

From (3), (5) and the preceding cap, even after dropping
the nonnegative prime \(x\) contribution we have
\[
 \sum_{\substack{x\in NJ,\ \mu^2(x)=1\\
                        \omega(x)\ {\rm odd}\ge3}}
        B(N-x)(\log x)Q_H(x)
              \le-(.3-o(1))T\mathfrak S(N).                      \tag{6}
\]
We verify that this signed statement yields the claimed
natural-scale number of actual pairs with a fixed rank and
a positive exponent floor on both legs.

Extend \(H\) smoothly with compact support to negative
arguments; this does not affect its values in the score.
In its Fourier integral a prime factor \(p\mid x\) enters
by \(1-e^{i\xi\log p/\log x}\), bounded by
\(a_\xi(p)=\min(2,C_J|\xi|\log p/L)\).
For fixed actual \(r\) use
[Henriot, Theorem 3](https://arxiv.org/pdf/1102.1643) with
its [erratum](https://doi.org/10.1017/S0305004114000280)
on the primitive forms \(m,N-rm\) on the real central
interval of length \(\asymp_J N/r\).
On the first form take the squarefree rough weight, with
prime values \(1_{p>z,\ p\nmid N}\); on the other take
\(t_0 a_\xi(p)1_{p\nmid N}\) on squarefree numbers for
any fixed \(t_0>1\).
Set all repeated prime-power values to zero.
Both nonnegative multiplicative functions have uniform
growth constants for each fixed \(t_0\).
The discriminant is \(N^2\) and the nontrivial bad local
factors at primes of \(N\) vanish by construction.
There are two roots away from \(Nr\), and one at its
primes, so the root product is bounded by
\(O(\mathfrak S(N)/L^2)\), with only the bounded extra
factor at the leading prime \(r\). The ordinary Euler
factor for the rough side is \(O(1/\eta)\) by prime
Mertens; for the Fourier side it is a fixed power of
\(2+|\xi|\), since
\(\sum_{p\le N}\min(2,C_J|\xi|\log p/L)/p
     \ll 1+\log(2+|\xi|)\).
The form coefficients are \(O(N)\) and the interval begins
and has length at a fixed polynomial scale, so the uniform
coefficient and interval ranges in the theorem apply.
Thus this positive enlarged sum at actual fixed \(r\) is
\(\ll_{t_0,J}(N/r)\mathfrak S(N)(2+|\xi|)^{O(t_0)}/(\eta L^2)\).
Fourier integration (rapid decay), the free \(\log x\le L\),
and the true \(r\)-harmonic then bound the entire
\(t_0^{\omega(x)}\)-tilted absolute score by
\(O_{H,J,\eta,t_0}(T\mathfrak S(N))\).
This pays all true ranks \(>K\) by \(O(t_0^{-K}T\mathfrak S(N))\).

For a genuine \(p\le N^\zeta\) dividing the squarefree \(x\),
\(p\) is a target unit and \(p\ne r\).
Open \(m=m_0+p k,\ x/p=x_0-r k\) on the exact progression,
with determinant \(p x_0+r m_0=N\).
This leaves the marked factor \(a_\xi(p)\) outside.
Both forms are primitive, both are positive in the actual
central interval, and its length \(\asymp_J N/(pr)\)
is still polynomial for any fixed small \(\zeta\).
The same Henriot upper applies with at most the bounded
extra local factor at the leading prime \(p\) (at \(p\),
\(m\) is nonzero). Excluding \(p\mid x/p\) keeps the
literal squarefreeness if desired. Sum \(a_\xi(p)/p
\ll |\xi|\zeta\) over the marked primes and integrate.
This bounds the true low-angle absolute tail by
\(O_{H,J,\eta}(\zeta T\mathfrak S(N))\).
No Fourier phase was separated using a constant own
logarithm, and no density assertion for joint primality
entered these tail bounds.

Choose \(K\) and then \(\zeta>0\) at the fixed preceding
parameters to make the two actual omitted tails smaller
than .1 of the scale in (6). The remaining \(y\) is
squarefree except possibly \(r\mid m\); its actual
\(r^2\mid y\) rows are \(N^{.5062+o(1)}\) with the
fixed divisor-power envelope and are negligible.
The resulting negative sum still has size \(\gg T\mathfrak S(N)\).
On each remaining true row, \(B(y)\le2\),
\(\log x\le L\), and \(|Q_H(x)|\le2^K\|H\|_\infty\).
By (2) there must therefore be
\(\gg N\mathfrak S(N)/L^2\) distinct requested pairs.

