# The two exact prime-tag sets in the critical odd-composite covariance

Let \(P\) run over even integers; use \(I=[P/3,2P/3]\), \(X=P/3,\ L=\log P,\ Q=\sqrt P/L^{20}\), \(n+r=P,\ n,r\in I\), and the Goldbach singular series \(S=S(P)\). Set
\[
 K(m)=\sum_{d\mid m,\ d\le Q}\mu(d),\quad B(m)=-\sum_{d\mid m,\ d\le Q}\mu(d)\log d,\quad
 R_z=1_{P^->z},\quad J_z=B1_{\mu=-1}R_z .
\]
Thus \(J_z\) vanishes on primes and on squareful/even-rank integers. This note evaluates signed **composite versus composite** subpopulations in [the actual polarized criterion](../odd_prime_covariance/Proof.md), without assuming independence of the two sign patterns. Covariance always uses the two *empirical* means: \(C(f,g)=\sum f(n)g(r)-XS\bar f\bar g,\ \bar f=X^{-1}\sum_{m\in I} f(m)\).

**Theorem 1 (literal bivariate total variation).** Fix sufficiently small \(t>0\), \(\epsilon=t^3,\ z=P^\epsilon\), and form the finite tag set
\[
 {\cal A}(m)=\{p\mid m:\ p\text{ prime},\ P^{t^2}<p\le P^t\}.
\]
For nonempty sets \(A,B\) of these prime labels put
\[
 D(A,B)=\sum_{{\cal A}(n)=A,\ {\cal A}(r)=B}J_z(n)J_z(r),\qquad
 m(A)=X^{-1}\sum_{n\in I,\ {\cal A}(n)=A}J_z(n).
\]
For either \(D(A,B)\) or \(D(A,B)-XS m(A)m(B)\), denoted \(D'(A,B)\), one has
\[
 \limsup_{P\to\infty}\frac1{XS}\sum_{A,B\ne\varnothing}|D'(A,B)|
       \le \exp\{-(.008+o(1))\,t^{-1}\log(1/t)\}\quad(t\downarrow0). \tag{1}
\]
Here both sets must be nonempty. This is the total variation of the signed table, **not** the absolute mass of individual physical summands. An arbitrary bounded function of the *two* exact sets, even nonseparable and chosen separately for every target, is allowed on this support. The reciprocal mass of the prime window is asymptotic to \(\log(1/t)\), which grows, and primes between \(P^{t^3}\) and \(P^{t^2}\) are expressly allowed. This is not a replacement by a narrower minimum-prime interval. On either marked support \(J_z=J_z-J_{P^\kappa}\) for \(\kappa=333/4000\); the latter is precisely the remaining middle weight of the criterion at its parameter \(t^6\).

There is also a fixed-exponent labeled test: fix \(0<a<b\le .008\), take \({\cal P}=(P^a,P^b]\cap\mathbb P\), \(z=P^\epsilon,\ \epsilon<a\); then
\[
 \lim_{\epsilon\to0}\limsup_P (XS)^{-1}
 \sum_{p,q\in{\cal P}}\left|\sum_{p\mid n,\ q\mid r}J_z(n)J_z(r)\right|=0.  \tag{2}
\]
The inner conditions here require divisibility by the specified labels, not exact equality of the tag sets. The two prime windows may differ within the same range.

**Theorem 2 (one literal set versus an untouched odd-composite population).** Set \(f=J_{P^{.050}}-J_{P^{.054}}\). Then
\[
 \limsup_P (XS)^{-1}\sum_{A\ne\varnothing}
 \left|\sum_{{\cal A}(n)=A}J_z(n)f(r)\right|
 \le\exp\{-(.023+o(1))\,t^{-1}\log(1/t)\}.                                  \tag{3}
\]
The same holds after subtracting \(XS m(A)\bar f\) inside the absolute value. Alternatively take \(f=J_z-J_{P^\kappa}\) on the **entire** remaining middle population: (3) then holds with .00004 in place of .023. Either variant has the single-label analogue of (2) with the relevant range \(0<a<b\le .023\) or \(b\le .00004\), summing only over the left label and retaining full \(f\) on the right. These comparisons say nothing unconditional about the sign of the unmarked complement or of Goldbach's count.

## 1. Marked short-divisor coefficients and ordinary signed means

All limits below take \(P\to\infty\) for each fixed \(\epsilon\), tag thresholds and degrees. Dependence of power-saving remainders on these parameters is harmless; the principal harmonic and sieve-width estimates will be uniform as \(t\to0\).

Let \(T\) be squarefree with \(h\) distinct tag primes, \(T\le P^\beta,\ \beta<1/2\). On \(T\mid n\) with \(h\ge1\), the true central prime contribution vanishes. By the complementary identity and moving-wall estimate in [critical parity transfer §1](../PanCriticalParityTransfer.md),
\[
 2 J_z(n)1_{T\mid n}=-LK(n)\mu^2(n)R_z(n)1_{T\mid n}
\]
up to a **summed**, not pointwise, absolute error \(o_\epsilon(X)\) in one dimension and \(o_\epsilon(XS)\) against any \(O_\epsilon(L)\) mate rough to \(z\). This remains true summed over the labels at fixed parameters: each \(n\) has only \(O_{\epsilon}(1)\) such subsets of prime divisors. After this step squareful rough and target-nonunit exceptions cost \(P^{1-\epsilon+o(1)}+P^{1/2+o(1)}\), also in ordinary means. For the genuinely unsigned envelope use always \(|J_z(n)|\le L R_z(n)\sum_{d\mid n,d\le Q}\mu^2(d)\); this bound also works at \(T=1\).

With \(R_z(d)\) understood, the normalized independent modulus coefficient is
\[
 \gamma_T(c)=\!\!\sum_{d\le Q,\,[T,d]=c}\mu(d),\qquad
 \Gamma_T(c)=\!\!\sum_{d\le Q,\,[T,d]=c}\mu^2(d).
\]
It is supported on squarefree multiples of \(T\), \(c\le Q T\); \(|\gamma_T|\le\Gamma_T\le 2^h\). The three actual sequences \(\gamma_T,|\gamma_T|,\Gamma_T\) all have this support. Write \(H_\epsilon=\prod_{z<p\le P}(1+1/p)\ll1/\epsilon\). The exact marked harmonic relation is
\[
 \sum_c\frac{\gamma_T(c)}c
 =\frac1T\sum_{g\mid T}\mu(g)
    \sum_{\substack{e\le Q/g\\(e,T)=1,\,R_z(e)}}\frac{\mu(e)}e .
 \tag{4}
\]
Indeed write \(d=ge,\ g=(d,T)\). The absolute harmonic sum with \(\Gamma_T\) is \(\le 2^h H_\epsilon/T\). Omitting \((e,T)=1\) costs \(o_{\epsilon,t}(1)\) in each inner sum uniformly in the labels, by marking a prime of \(T\); the tag lower endpoint is a fixed positive exponent. For \(g\le P^\beta\) the remaining signed sum is \(\rho(\log(Q/g)/\log z)+o_{\epsilon,t}(1)\), uniformly in the endpoint on this compact range. This is the [signed prime-simplex expansion](../PanGlobalRoughTransfer.md): the positive and negative parts have convergent finite prime-simplex sums, continuous away from the initial atom, giving uniform convergence of cumulative functions on compact positive intervals. In particular the modulus of (4) is at most
\[
 (2^h/T)(d_\epsilon+o_{\epsilon,t}(1)),\qquad
 d_\epsilon=\rho((.49-\beta)/\epsilon),
\]
for the stated small \(\beta\), where \(\rho(u)\le 1/\lfloor u\rfloor!\). The useful cancellation in (4) is within each *fixed* label product, not between different tags. For a prime-tag family of reciprocal mass \(\lambda_P=\sum_{p\in{\cal P}}1/p\), the harmonic mass of the products of degree \(h\) is at most \(\lambda_P^h/h!\). By Mertens, \(\lambda_P\to\lambda=\log(1/t)\) in (1),(3); in (2) it stays bounded for fixed \(a,b\).

## 2. Signed bilinear dispersion while keeping the label products fixed

Here \(\beta=.008,\ \eta=.0001,\ D=P^\eta,\ s=\eta/\epsilon\). Open \(K_Q(n)1_{T\mid n},K_Q(r)1_{U\mid r}\) on \(z\)-rough inputs as above. The outside scale \(L\) on each side is retained. For fixed \(T,U\le P^\beta\), apply the [critical signed short–short beta-sieve/CRT argument](../PanCriticalCompositePolynomialSieve.md), using the independently supported coefficients \(\gamma_T,\gamma_U\), and separately the unsigned \(|\gamma_T|,|\gamma_U|\) for the upper-minus-lower width. For bounding an unsigned physical factorial moment use \(\Gamma_T,\Gamma_U\) with the upper sieve. Take a target-unit right coefficient; the shared-target exceptional rows were already disposed of. On any compatible pair of large divisors the small-prime exclusion density is \(2/\ell\) for \(\ell\nmid P\), \(1/\ell\) for \(\ell\mid P\). Its product is \((1+o_\epsilon(1)) S V_0^2,\ V_0=\prod_{\ell\le z}(1-1/\ell)\asymp1/(\epsilon L)\), uniformly in the target. The fundamental-lemma widths are \(O(s^{-s/2})\) relative to this product with an absolute constant for large \(s\). Use a central bump with endpoint transitions of width \(P/L^M\) and derivatives bounded by log powers; the true absolute costs of restoring all tags are controlled by fixed divisor moments, with no endpoint error paid on each pair of labels.

Crucially, the complete bound can be summed **absolutely over \(T,U\)**, not merely against factorizable label signs. For each beta divisor \(w\le D\) assign its primes to the left/right as in the cited argument (a prime dividing \(P\) is assigned only to the left). On a dyad of extended moduli \(b\asymp B,c\asymp C\), the independent coefficients have norms
\[
 \|\alpha\|_2\ll L2^h\sqrt{B/T},\qquad
 \|\alpha'\|_2\ll L2^j\sqrt{C/U},\qquad j=\omega(U).
 \tag{5}
\]
Indeed their moduli are multiples of \(T,U\), including when the original short divisor shares factors with a tag; each beta allocation is fixed, so division by its known factors recovers the marked coefficient. A nonempty dyad has \(B\gg T,\ C\gg U\). The absolute bounding coefficients satisfy the same estimate. The two exponents of \(B,C\) are at most \(m=.5+\beta+\eta+o(1)=.5081+o(1)\).

For \(BC\ge P\), apply the published [Bettin–Chandee Theorem 1](https://arxiv.org/abs/1502.00769) with both signs of the actual shift \(P\) after Poisson, exactly as in [the shoulder proof §3](../PanSupercriticalShoulder.md). The two discrepancy exponents relative to \(P\) are at most \((33m-17)/20,\ (15m-8)/8\), up to arbitrarily small fixed slack. The full Mellin separation, frequency dyads, and \(L^1\) bounds are in that proof; they are linear in the two coefficient norms, so (5) multiplies these errors by \(O_{h,j}((TU)^{-1/2})\). Summing over all label products cannot cost more than \((\sum_{T\le P^\beta}T^{-1/2})^2\ll P^\beta\), since distinct squarefree products are distinct integers. The allocations cost \(\ll P^\eta(1+\log P)\). After these two losses *both* exponents are below \(-.003\). When \(P^{.98}\le BC<P\), work directly at first frequency dyad \(F=1\): the factor \(H^{-1}(1+F/H)^{1/2}\), \(H=BC/P<1\), is absorbed by arbitrarily high Fourier decay at \(F/H\). The two unnormalized exponents are at most \(.85+.25m,\ .875+.125m\), from (4) of the shoulder proof with \(F=1\). With the same sparse gains and losses both are below .99. The \(F>1\) sum converges by taking extra derivatives. If \(BC<P^{.98}\), bounded variation gives \(O(1)\) error per ordinary CRT progression; even ignoring sparsity the total exponent is at most \(.98+2\beta+\eta<.997\). This proves the required power saving **after summing all labeled errors**, even in the presence of nonseparable external signs. No absolute summation over the underlying marked divisor moduli in the signed spectral estimate is asserted.

The signed main for compatible labels is \(XS(L V_0)^2(\sum\gamma_T/c)(\sum\gamma_U/c')\) up to negligible normalized errors after summing the relevant labels. To check coprimalities explicitly, if \(T,U\) share a prime, physical rows require it to divide \(P\), already negligible, and we may omit this label pair from the raw sum. Otherwise a cross common prime not in \(TU\) is paid by \(\ll\sum_{p>z}p^{-2}\) in the two harmonic sums over \(e\) in (4); one in \(T\) or \(U\) by \(\ll\sum_{p\mid TU}1/p=o_{\epsilon,t}(1)\) on the other side. For \(T,U\) coprime to \(P\), omissions due to \((c',P)>1\) cost \(\sum_{p\mid P,p>z}1/p=o_{\epsilon,t}(1)\); tag products sharing \(P\) have total reciprocal mass \(o_{\epsilon,t}(1)\) at each fixed degree. All such estimates carry the outside harmonic factors \(2^{h+j}/(TU)\), so are summable. For an upper bound for a wholly unsigned main, simply drop all coprimalities. The corresponding one-variable beta sieve uses \(V_0\), with summed floor errors power small: for each \(T\) one may sum directly over \(d\le Q\) and \(w\le D\), then over \(T\le P^\beta\). Its literal variance/signed-error width uses the same absolute majorants.

Here is a summary of the bounds, to track uniform constants when the factorial degrees grow. Let \(a_h=(2\lambda)^h/h!\) (set \(a_0=1\)). For \(h,j\ge1,\ ht,jt\le\beta\), the limsup of the raw **sum of moduli over degree-\(h,j\) label pairs** of the signed physical marked \(J_z,J_z\) sums, divided by \(XS\), is
\[
 \ll \epsilon^{-4}\{d_\epsilon^2+s^{-s/2}\}\,a_h a_j.                       \tag{6}
\]
This follows from the signed means (4) and the width bound using \(\Gamma\); the factors \(-1/2\) from the complementary identities are harmless. The same argument bounds the wholly unsigned physical factorial moment for \(h,j\ge0\) by \(\ll\epsilon^{-4}a_h a_j\), **without** requiring either signed identity. The analogous bounds on one ordinary signed/unsigned left margin, divided by \(X\), are \(\ll\epsilon^{-2}(d_\epsilon+s^{-s/2})a_h\) for \(h\ge1\), resp. \(\ll\epsilon^{-2}a_h\) for \(h\ge0\). The implied constants for these displayed principal bounds are absolute for sufficiently large \(s\): use \(H_\epsilon\ll1/\epsilon,\ LV_0\ll1/\epsilon\); the factors \(2^{h+j}\) are already in \(a_h a_j\). The \(O_{t,h,j}(P^{1-c})\) arithmetic errors have disappeared under the first limit. For (2) take \(h=j=1\), fixed \(a,b\), with the same proof and the bounded \(\lambda=\log(b/a)\); then send \(\epsilon\downarrow0\). If \(\lambda=0\) the assertion is empty.

## 3. From factorial moments to the two *exact*, unweighted tag sets

This is not a product test. For every \(P\) take any real table \(|\Psi(A,B)|\le1\), zero when either set is empty. Its Boolean-lattice expansion is
\[
 \Psi(A,B)=\sum_{T\subseteq A,\ U\subseteq B} c(T,U),\qquad
 |c(T,U)|\le 2^{|T|+|U|},\qquad c(\varnothing,U)=c(T,\varnothing)=0 .
\]
Here labels in subsets are identified with their squarefree products. Truncate to \(|T|,|U|\le k=\lfloor\beta/t\rfloor-1\), so even the first omitted factorial orders \(k+1\) on both axes have products within the available rails. The signed contribution of this polynomial is, by (6), at most an absolute constant times \(\epsilon^{-4}(d_\epsilon^2+s^{-s/2})e^{8\lambda}\) in the normalized limsup.

When \(i=|A|>k\), for \(h\le k\) one has \(\binom ih\le\binom{k+1}h\binom i{k+1}\). Thus on this tail the absolute truncated left factor is bounded by \(3^{k+1}\binom i{k+1}\), the right factor by \(\sum_{j\le k}2^j\binom{|B|}{j}\), and the true selector itself by 1. Interchange the axes for the remaining tail. The **unsigned** factorial moment bound therefore gives tail at most
\[
 O\!\left(\epsilon^{-4}(1+3^{k+1}e^{4\lambda})\frac{(2\lambda)^{k+1}}{(k+1)!}\right).
\]
The one-dimensional Boolean expansion proves the same-form bound on \(\sum_{A\ne\varnothing}|m(A)|\) (allow \(d_\epsilon\) rather than its square). Now \(\lambda=\log(1/t),\ k+1=\lfloor\beta/t\rfloor,\ \epsilon=t^3\). Elementary factorial growth gives the exponent \(-(\beta+o(1))\log(1/t)/t\) for the tail. Both Dickman and fundamental-lemma errors decay faster than this scale. Choose \(\Psi\) to be the sign of each \(D(A,B)\); for centering apply also the one-variable bound to the product of empirical means. This proves (1), with all exponent constants referring to the order of limits specified. In particular arbitrary changes of sign between the different *physical* exact-label cells do not undo this cancellation.

## 4. One labeled side versus the entire other weight

For the interior min-prime band of Theorem 2 use \((\beta,\eta)=(.023,.0005)\). The proof of [critical parity transfer, §3](../PanCriticalParityTransfer.md) gives for this \(f\), and its unsigned envelope \(F=L\tau\mu^2 1_{P^{.050}<P^-\le P^{.054}}\), arbitrarily log-small absolute discrepancy over \(q\le P^{.5+\beta+\eta}\), \((q,P)=1\), at the common residue \(P\bmod q\). Specifically mark one prime in the indicated window with reciprocal multiplicity, retaining independent roughness/oddness and divisor conditions as in [the polarized proof §1](../odd_prime_covariance/Proof.md). The short-prime exponent \(x\in[.050,.054]\) has \((1+x)/2\ge.525,\ 4/7-6x/7\ge.52514\ldots\), strictly above .5235, so [Fouvry, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf) suffices for every dyad; the genuine short prime has the required SW estimates. For \(f=J_z-J_{P^\kappa}\) use \((\beta,\eta)=(.00004,.000005)\); .500045 is inside the .50005 rail established by the Fouvry and macroscopic Fouvry–Radziwiłł arguments of the polarized proof for the complete band. In both cases \(|f|\le F\) with \(\sum F\ll X\epsilon^{-2}\) uniformly by the two-rough-factor hyperbola (the interior band even has \(O(X)\) with an absolute fixed constant).

For a marked left short divisor \(c\) now \(c\le Q P^\beta\); sieve the opposite-to-\(f\) left variable to \(z\) at level \(P^\eta\). The combined moduli are \(cw\), and \(w\) is exactly the small-prime part, so each such modulus fixes \(c\). When summing discrepancy *over all tag products \(T\) of fixed degree*, the number dividing \(c\) is bounded in terms of the fixed tag lower exponent (all such prime divisors exceed \(P^{t^2}\) or \(P^a\)); also \(\Gamma_T(c)\le 2^h\). The right total absolute discrepancy can absorb these fixed multiplicities and the outside log. It is not multiplied by \(P^\beta\). The actual right inputs are \(z\)-rough, hence \((r,cw)=1\) reduces to \((r,c)=1\) in the principal row. After removal of shared target rows the local product on the left is \((1+o_\epsilon(1))SV_0\). Uniformly in \(r\), \(c/\phi(c)=1+o_\epsilon(1)\) on the squarefree rough support; omitting \((c,Pr)>1\) from the marked harmonic sums costs \(o_{\epsilon,t}(1)\) after all labels are summed. In detail, \((T,Pr)>1\) is exceptional with harmonic mass bounded by a fixed factor times \(\sum_{p\mid Pr,\ p>P^{t^2}}1/p=o_t(1)\); remaining exclusions in (4) cost \(\ll H_\epsilon\sum_{p\mid Pr,p>z}1/p\). These bounds apply to \(F\) as well as \(f\), and the signed-sieve majorant is costed through its positive-envelope upper-minus-lower width.

Consequently the one-axis analogue of (6) against \(f\) is \(\ll\epsilon^{-4}(d_\epsilon+s^{-s/2})a_h\) for \(h\ge1\) and its unsigned moment is \(\ll\epsilon^{-4}a_h\), with absolute principal constants in either stated variant. Use the one-dimensional Boolean argument of §3, \(\lfloor\beta/t\rfloor-1\) retained degrees, the empirical ordinary bounds (using the same one-variable rail) and \(|\bar f|\ll\epsilon^{-2}\). This proves (3) and the fixed-exponent single-label statement, with the orientation and two different rails as stated.

The Poisson dispersion estimate, beta sieve and generalized SW distribution inputs are classical or explicitly cited prior applications. The specific conclusion here is signed total variation after revealing actual factor labels at the prescribed target and both physical inputs, not a new generic level of distribution. It does not allow a selector to inspect the residual cofactors once the two tag sets are known, and it excludes the empty-set cells indicated in each theorem. For a small independent check of the parameter arithmetic and combinatorial identities run **python3 -O verify.py** beside this file; the asymptotic analytic statements do not rest on numerical estimation.

**Comparison checked through November 21, 2026.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) treats weighted Type I, balanced rough-pair benchmarks, multiplicative markers and a separate sharp covariance criterion; [Arneth, October 20 v1](https://zenodo.org/records/23504447) formulates a signed parity-separation problem. The estimate above is restricted to the actual short Pan weights on the stated nonempty tag cells, does not settle either broader correlation problem, and makes no priority claim about the dispersion inputs.
