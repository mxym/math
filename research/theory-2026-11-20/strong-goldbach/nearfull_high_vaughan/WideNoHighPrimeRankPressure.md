# A prime-opponent rank constraint on the exact wide no-high remainder

Let \(N\) be an individual even target, \(L=\log N\), and let
\(J\subset[1/3,2/3]\) be a fixed interval of positive length. Put
\(y=N-x\), \(M=|J|N\mathfrak S(N)\), and
\[
 \langle V,W\rangle_J=
 \sum_{\substack{x\in NJ\\(x,N)=1}}V(x)W(y),\qquad
 \Pi(n)=(\log n)1_{n\ {\rm prime}},\qquad
 R_J=\langle\Pi,\Pi\rangle_J.
\]
Use the original wide affine profile and parameters of
[the wide no-high decomposition](WideLowNoHighRemainder.md):
\(\lambda=.006\), \(U=N^\lambda\), \(k=(1-\lambda)^{-1}\),
\(\rho=.518\), \(v=.498\), \(w=.499\), and
\(F(t)=(1+kt)C(t)\). Here \(C\) is a fixed smooth **nonincreasing**
cutoff in \([0,1]\), equal to 1 through \(.486\) and 0 from
\(.490\) on. Monotonicity is used for the exact rank-three sign,
not for the covariance calibration.

Write \(P\) for the whole composite-only true mark score,
\(\mathcal L\) for its part with \(U<r\le N^\rho\), and
\(E=\mathcal L-P\) for the nonnegative high affine weight,
as in the cited decomposition.
In that same theorem take the smooth allowed product cap:
let \(\chi\) be a fixed smooth function in \([0,1]\), equal to 1
through \(.4985\) and 0 from \(.499\) on, and put
\[
 B_\chi(n)=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\U<r\le N^v}}
 (\log r)\sum_{d\mid n/r}\mu(d)
 F\!\left(\frac{\log(dN/n)}L\right)
 \chi\!\left(\frac{\log(rd)}L\right),\qquad
 T=\mathcal L-B_\chi.
\]
Thus \(T\) is a literal remainder for this chosen cap and still
vanishes exactly on every central \(n\) with a true prime factor
\(>N^\rho\). The same score occurs in the binary covariance identity
of the cited theorem; here we estimate a different, actual
prime-opponent pairing.

**Theorem.** Fix the profiles and \(J\) as above. There are
\(0<\eta<.01\) and a fixed integer \(K\ge4\) such that
at every sufficiently large even \(N\) with \(R_J\le .01 M\),
\[
 \sum_{\substack{x\in NJ,\ (x,N)=1\\
         x\ {\rm squarefree},\ P^-(x)>N^\eta\\
         4\le\omega(x)\le K,\ P^+(x)\le N^{.518}}}
       T(x)\Pi(N-x)>.36 M.                                      \tag{1}
\]
In particular there are \(\gg_J M/L^2\) genuine such rows on
which \(T(x)>0\) and \(N-x\) is prime (constants may also depend
on the fixed profiles). The sharp product cap of the earlier theorem
has the same exact rank-two and rank-three restrictions below,
but the fixed-rank truncation in (1) is asserted only for the
smooth-cap representative. No estimate on
\(\langle T,T\rangle_J\) follows from (1): in fact the opposite
\(T(N-x)\) vanishes on every row counted here.

## 1. The true prime pairing

Ordinary prime Bombieri–Vinogradov, in the same actual
\(q=rd\le N^{.499}\) expansion, gives
\[
 \langle B_\chi,\Pi\rangle_J
 =-k(v-\lambda)M+o(M).                                           \tag{2}
\]
This is the prime calculation of the
[wide no-high decomposition, §3](WideLowNoHighRemainder.md).
One may use the true \(\Pi\) directly instead of
\(F(\log(N/y)/L)\Pi\): at each fixed real spatial argument
the same reduced principal is \(-k(v-\lambda)\mathfrak S(N)
+o(\mathfrak S(N))\) before either multiplier is integrated.
The cap is identically one on the completed \(d\le S\) box,
\(S=\exp((\log L)^4)\); the true \(d\) tails use its bounded
variation. The shared \(r\mid d\) part of the principal costs an
additional reciprocal prime power, with \(r>U\).
Here and below no claim is made about such an approximation
pointwise on an individual physical row.

The actual one-prime calibration also gives
\(\langle P,\Pi\rangle_J=-R_J+o(M)\).
Indeed \(a_F=F(0)-(1-\lambda)F'(0)=0\) in the
[short-endpoint calculation, §2](WholeSuperrootPrimeTransfer.md).
Applied to the genuine prime source \(y=N-x\), the expanded moduli
are at most \(N^{\lambda+.490}=N^{.496}\), and the ordinary
prime BV mean is the genuine reduced mean; actual prime divisors
of \(N\) are excluded. The residual proper prime-power terms in
\(A_F=P+F(\log(N/x)/L)\Pi\) occupy \(N^{1-\lambda/2+o(1)}\)
integers, so contribute \(o(M)\). On the genuine binary atom
the spatial multiplier is \(1+O_J(1/L)\); the classical
fixed-target upper sieve \(R_J=O_J(M)\) makes its replacement
by 1 harmless. Equivalently this is the prime-source part of
[the two-endpoint calibration](JointGiantEndpointDerivative.md).

Consequently the exact decomposition \(T=P+E-B_\chi\) yields
\[
 \langle T,\Pi\rangle_J
   =k(v-\lambda)M-R_J+\langle E,\Pi\rangle_J+o(M).              \tag{3}
\]
We use only the pointwise nonnegativity of \(E\), not a model
for its pairing with the actual prime.

## 2. Literal low ranks

Put \(\kappa=\log(N/x)/L=O_J(L^{-1})\) and use target-log
angles, so that the sum of all factor angles is \(1-\kappa\).
Because \(C\) is nonincreasing and \(1+kt\) is positive,
\[
          F(t+a)-F(t)\le k a\qquad(t,a\ge0).                    \tag{4}
\]
In the affine region equality holds. The following statements
are pointwise, including any ties at the caps.

* A true central prime has \(T=0\). On a squarefree product
  of three genuine primes, **each individual mark's contribution
  to \(T\) is nonpositive**. For \(r\le N^v\) the \(d=1\) term
  is removed because its cap is 1. The \(d\) consisting of
  both quotient factors has argument \(1-\log r/L\ge .502\),
  outside \(F\). Each remaining singleton \(d\) enters with
  sign minus, a nonnegative multiplier \(1-\chi\), and
  \(F\ge0\). For \(r>N^v\), its whole quotient score occurs
  without a cap. If the quotient factors have angles \(a\le b\),
  then \(a\le .251\) and \(F(\kappa+a)-F(\kappa)=ka\)
  for large \(N\). Apply (4) at \(t=\kappa+b\) to obtain
  \(F(\kappa)-F(\kappa+a)-F(\kappa+b)+F(\kappa+a+b)\le0\).
  A mark outside the original \(U<r\le N^\rho\) range is
  absent, not assigned a sign. In particular no least-factor
  condition on the squarefree triple is necessary.
* Write a true squarefree semiprime as \(x=ab\), \(a<b\),
  with target-log angles \(u,z\), respectively. On the nonzero
  support the larger angle is \(z\le.518\) and \(z>.498\)
  for large \(N\). If \(u\le.498\), only the larger mark can
  contribute to \(T\): the smaller mark's constant is capped
  and the possible \(d=b\) has angle outside \(F\).
  The resulting exact score is
  \[
          \frac{T(x)}L=z\big(F(\kappa)-F(1-z)\big).
  \]
  If \(z\ge .514\) then \(1-z\le .486\) and this is
  nonpositive. Thus the positive part in this case has
  \(u\ge .486-O_J(1/L)\) and is bounded by
  \((.514+O_J(1/L))L\). If \(u>.498\), both marks enter
  and the nonconstant divisor term for each is outside
  \(F\); the positive part is at most \((1+O_J(1/L))L\).
  These restrictions hold for the sharp cap as well.

The audited
[true prime-opponent angular upper](../angular_prime_first_composite/Proof.md)
with coefficient \(3.446\) applies to this positive squarefree
rank-two part. All factors in its support are genuine primes
in compact positive angles, with fixed outward Jordan
approximation at the endpoints. Against the ordinary ordered
rank-two source, the normalizing density is
\(du/[u(1-u)]\), by PNT in the larger actual prime and
prime reciprocal harmonic in the smaller one. The spatial
restriction is to the same fixed \(J\); using \(L\) in
place of the actual central logs has relative error \(O_J(1/L)\).
The density is below \(4.01\) on the limiting region
\(u\in[.486,.5]\). We get
\[
 \begin{split}
 &\sum_{\substack{x\in NJ,(x,N)=1\\x\ {\rm squarefree},\ \omega(x)=2}}
             T(x)_+\Pi(N-x)\\
 &\qquad\le\big(3.446\cdot4.01\{.012\cdot .514+.002\}
                    +o(1)\big)M< .114 M.                        \tag{5}
 \end{split}
\]
The decimal product before the \(o(1)\) is \(0.11286918128\).
In particular this is an upper on a true two-prime-product
source against a true prime, not a marginal prediction.
The spatial cutoff and target units remain those of (3).

## 3. Remove the physical tails for the smooth cap

Extend \(F\) and \(\chi\) smoothly and compactly to the real line,
without changing them on nonnegative arguments. For real \(t\)
and \(p\le N\) put
\[
 w_t(p)=|1-e^{it\log p/L}|+\frac{\log p}L,
 \qquad W_t(n)=\prod_{p\mid n}w_t(p).
\]
The envelope used in
[the mixed rank reservoir, §2](WideAffineMixedRankReservoir.md)
holds for \(\mathcal L\): \(2L\int|\widehat F(t)|W_t(n)\,dt/(2\pi)\).
For \(B_\chi\) the corresponding envelope is
\[
    2L\iint |\widehat F(t)\widehat\chi(s)|
             W_{t+s}(n)\,\frac{dt\,ds}{(2\pi)^2}.              \tag{6}
\]
Indeed the actual phase \(r^{is/L}\) has modulus one and the
divisor Euler product is now
\(\prod_{p\mid n/r}(1-e^{i(t+s)\log p/L})\). On \(r\parallel n\)
allocate the actual \(\log r/L\) to its degree-one term in
the positive expansion of \(W_{t+s}(n)\). On \(r^2\mid n\)
the product still contains \(r\), and the normalized repeated-mark
weights sum to at most one. This proves (6) with the true cap
and without a squarefree assumption. The two fixed Schwartz
transforms have enough moments of every order.

For completeness the required actual mixed upper applies
[Henriot's Theorem 3](https://arxiv.org/pdf/1102.1643)
with the [erratum](https://doi.org/10.1017/S0305004114000280)
to the two primitive affine forms \(x,N-x\).
On the prime leg, majorize \(\Pi(N-x)\) by \(L\) times the
multiplicative \(N^{.01}\)-rough indicator, zero at all positive
powers of primes dividing \(N\). On \(x\) use the multiplicative
weight \(\theta^{\omega(x)}W_t(x)\), with \(\theta>1\) fixed,
again zero at target primes. The multiplicative growth bound at
positive powers is \(3\theta\). The resultant is \(N\). At
primes dividing \(N\) the coinciding root is excluded by the unit
weights (including at 2); the relative local
product is \(\ll\mathfrak S(N)/L^2\) as in the cited mixed
envelope. Its remaining good-prime product for the prime leg
is bounded, and
\[
  \prod_{p\le N}\left(1+\frac{\theta w_t(p)}{p-1}\right)
       \ll_\theta (2+|t|)^{O_\theta(1)}.
\]
This follows by splitting the prime harmonic where
\(|t|\log p/L\) reaches 1 and using
\(|1-e^{i a}|\le\min(2,|a|)\). The prime leg's \(L\)
and the envelope's \(L\) cancel the two sieve logarithms.

If additionally a true \(p\mid x\), \(p\le N^\eta\),
\(0<\eta\le .01\), substitute \(x=pv'\). Actual units force
\(p\nmid N\) and \(p\ne2\). The forms \(v'\) and \(N-pv'\)
are primitive, retain resultant \(N\), and have only the extra
leading prime \(p\). At \(p\) the second form is a nonzero
constant and the first has one root; the relative factor
is bounded. The true interval length is \(\asymp_J N/p\),
within the corrected theorem's power-length range. Extract
\(w_t(p)\) once, replacing the first form's multiplicative
weight at every positive \(p\)-power by 1 (also when \(p^2\mid x\)).
The sum of the resulting extra factors is
\(\sum_{p\le N^\eta}w_t(p)/p\ll\eta(1+|t|)\).
Integrating the one- and two-transform envelopes gives
\[
 \sum_{P^-(x)\le N^\eta}|T(x)|\Pi(N-x)\ll_J \eta M,\qquad
 \sum_{\omega(x)>K}|T(x)|\Pi(N-x)\ll_{J,\theta}\theta^{-K}M,   \tag{7}
\]
with the actual spatial and unit conditions in both sums and
constants allowed to depend on the fixed profiles. No sharp
product-cutoff bound is used in (7).

After fixing \(\eta>0\), the nonsquarefree \(x\) left in the
rough part number \(O(N^{1-\eta}+\sqrt N)\) by the true large
prime-square count. Their weights cost \(N^{o(1)}\) per row,
hence \(o(M)\). Choose fixed \(K\) sufficiently large and then
fixed \(\eta\) sufficiently small that the combined absolute
loss in (7) is less than \(.008M\). Apply (3) with
\(R_J\le .01M\), then subtract (5); discarded squarefree
triples were nonpositive and primes had zero score. Since
\[
      \frac{.492}{.994}-.01-.114-.008>.36,
\]
the remaining signed sum satisfies (1). Its physical no-high
condition is exact by the cited decomposition. At fixed
squarefree rank \(K\) each summand is \(O_K(L^2)\), giving
the claimed positive-row count without replacing the signed
sum by a product model.
