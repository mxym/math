# Quantitative almost-all calibration of the central Goldbach kernel

This is a classical circle-method consequence organized to give a simultaneous bound for moving summand windows and the entire old central operator. No GRH, no genuinely new estimate on minor arcs, no all-target claim. It quantitatively complements [CentralMeanSquare.md](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/CentralMeanSquare.md), whose §§2–4 give a fixed-test-function/Green–Tao density limit and an additional fixed-local-model exact variance (that variance is not part of this note).

## Theorem

Let \(w(k)=\log k\) on primes and zero otherwise, \(w(0)=w(1)=0\). Let \(S(N)\) be the binary singular series. For every fixed \(A,B>0\), and all sufficiently large integer \(X\), there is a set \(\mathcal E_X\) of at most \(O_{A,B}(X(\log X)^{-A})\) even integers in \([X,2X]\) such that, simultaneously for all even \(N\in[X,2X]\setminus\mathcal E_X\) and every \(0\le a\le b\le1\),
\[
\left|\frac1N\sum_{aN\le k\le bN}w(k)w(N-k)-S(N)(b-a)\right|
\ll_{A,B} S(N)(\log X)^{-B}.
\tag{1}
\]
The intervals' endpoints may depend arbitrarily on the target and terms at endpoints can be included, excluded, or half-weighted. In particular, for the old central operator (including its original coprime von Mangoldt version),
\[
\frac{\|T_N\|_{\rm op}}{S(N)}\le\frac{\|T_N\|_{\rm HS}}{S(N)}
\ll_{A,B}(\log X)^{-B}\quad(N\notin\mathcal E_X).
\tag{2}
\]
The same simultaneous exceptional set controls every summand window and every kernel coordinate pair, not just finitely many originally fixed test functions. The analogous dyadic mean of \((\|T_N\|_{\rm HS}/S(N))^2\) decays faster than any fixed inverse power of \(\log X\). The old qualitative mean-square theorem is therefore strengthened in quantitative rate, not in pointwise scope.

## 1. Fixed-prefix Fourier expansion

Write \(\ell=\log(2X)\), \(J=\lceil\ell^{B+1}\rceil\), \(y_i=iX/J\) for \(0\le i\le2J\), and \(Q=\lfloor\ell^K\rfloor\), where \(K\) will be chosen depending on \(A,B\) (for example \(K>2A+7B+30\)). Set \(e(x)=e^{2\pi i x}\), \(P_y(\alpha)=\sum_{0\le k\le y}w(k)e(k\alpha)\), and \(V_y(\beta)=\int_0^y e(\beta t)\,dt\). For each \(y=y_i\), the exact target prefix
\[
C_y(N)=\sum_{0\le k\le y}w(k)w(N-k)\qquad(w(r)=0\ \text{for }r<0)
\]
is the \(N\)-th Fourier coefficient of \(P_yP_{2X}\) for \(0\le N\le2X\). In particular, the second Fourier factor always has the same fixed cutoff \(2X\); dependence of the summand window on \(N\) enters only after the exceptional sets are constructed.

Use the common major arcs on \(\mathbb R/\mathbb Z\) with centres \(a/q\), \((a,q)=1,\ 1\le q\le Q\), and common half-width \(Q/X\). For all large \(X\) these arcs are disjoint since their distinct centres are separated by at least \(Q^{-2}\) on the torus and \(2Q^3<X\). Their complementary minor arcs are also common for all \(N\) and \(y_i\). These auxiliary arcs need not coincide with the older project's sharp arcs because the full Fourier coefficient is exact.

## 2. Major arcs, including all denominators in the tail

Use the standard Siegel–Walfisz theorem in the strength
\[
\sum_{\substack{k\le z\\k=r\bmod q}}w(k)
=z/\phi(q)+O_{K,D}(X\ell^{-D})\qquad(0\le z\le2X,\ q\le Q,\ (r,q)=1),
\]
for arbitrary \(D>0\). For \(z\ge\sqrt X\), the usual \(q\le(\log z)^{K+1}\) condition holds as \(X\to\infty\), and one may enlarge the saving in the usual theorem; for smaller \(z\) the trivial total Chebyshev bound suffices. The difference between prime log and von Mangoldt versions is negligible at this scale. Summing over reduced residues with phase \(e(ar/q)\), whose sum is \(\mu(q)\), and partial summation in \(z\) for the twist \(e(\beta z)\), yields
\[
P_y(a/q+\beta)=\frac{\mu(q)}{\phi(q)}V_y(\beta)
 +O_{K,D}(X\ell^{-D})\qquad(|\beta|\le Q/X,\ 0\le y\le2X)
\tag{3}
\]
with any desired \(D\); choose the original Siegel–Walfisz power large enough to absorb the number \(q\) of residues and the \(1+O(Q)\) partial summation loss. Primes dividing \(q\), not in the reduced residues, have total log weight at most \(\log q\).

The total measure of the major arcs is \(O(Q^3/X)\). Since \(P_y,V_y\ll X\) for all \(y\le2X\), the integrated product error from (3) is \(O_{K,D}(X Q^3\ell^{-D})\), uniformly in the target. The main part is
\[
S_Q(N)\int_{-Q/X}^{Q/X}V_y(\beta)V_{2X}(\beta)e(-N\beta)\,d\beta,
\quad S_Q(N)=\sum_{q\le Q}\frac{\mu(q)^2c_q(N)}{\phi(q)^2}.
\tag{4}
\]
Here \(c_q(N)=\sum_{(a,q)=1}e(aN/q)\) is the real Ramanujan sum. The full integral over the real line equals \(\min(y,N)\) for \(X\le N\le2X\): continuous Fourier inversion of the convolution of the two interval indicators gives the length of \([0,y]\cap[N-2X,N]\). The inversion is legitimate since this convolution is continuous and the product transforms are integrable. The removed tails cost \(O(X/Q)\) by \(|V_y(\beta)V_{2X}(\beta)|\ll |\beta|^{-2}\).

For each even \(N\), the full Ramanujan series converges absolutely and expands into the usual Euler product \(S(N)\). For its absolute series the prime factor is \(p/(p-1)\) if \(p\mid N\), and \(1+(p-1)^{-2}\) otherwise. For \(p>2\) dividing \(N\), \(p/(p-1)\le(p-1)/(p-2)\); the fixed convergent product of the other factors, including the factor at 2, gives \(|S_Q(N)|\ll S(N)\) uniformly.

Do **not** claim a uniform power-of-log bound for the omitted tail on every target. Instead, for squarefree \(q\), primewise multiplication or \(c_q(N)=\sum_{d\mid(q,N)} d\mu(q/d)\) gives
\[
\sum_{1\le N\le2X}|c_q(N)|
\le\sum_{d\mid q}d\lfloor2X/d\rfloor
\le2X\,\mathrm d(q),
\]
where \(\mathrm d(q)\) is the number of divisors. Using \(\mathrm d(q)\ll_\epsilon q^\epsilon\), \(\phi(q)\gg_\epsilon q^{1-\epsilon}\) with \(\epsilon=1/6\), one obtains by absolute summation
\[
\sum_{1\le N\le2X}|S_Q(N)-S(N)|
\ll X\sum_{q>Q}\frac{\mathrm d(q)}{\phi(q)^2}
\ll XQ^{-1/2}.
\tag{5}
\]
In particular \(|S_Q(N)-S(N)|\ll\ell^{-B}\) for all but \(O(X\ell^B Q^{-1/2})\) targets, one exceptional set independent of \(y\). Since \(S(N)\gg1\) for even \(N\), (3)–(5) show uniformly in \(y\) that the major-arc integral is \(S(N)\min(y,N)+O_{A,B}(S(N)X\ell^{-B})\) for these targets.

## 3. Minor arcs and the simultaneous grid

On the complementary minor arcs, Dirichlet's approximation with denominator cap \(\lceil X/Q\rceil\) supplies a reduced rational \(a/q\) with \(Q<q\le\lceil X/Q\rceil\) and \(|\alpha-a/q|\le q^{-2}\), taking distance on the torus. Indeed the approximation has error at most \(1/(q\lceil X/Q\rceil)\le Q/(qX)\); if its denominator were at most \(Q\), \(\alpha\) would lie on a major arc. The classical Vinogradov–Vaughan estimate gives
\[
|P_{2X}(\alpha)|\ll \ell^4(X/\sqrt q+X^{4/5}+\sqrt{Xq})
\ll_K XQ^{-1/2}\ell^4,
\]
absorbing \(X^{4/5}\) for large \(X\). One may apply it to von Mangoldt and remove its \(O(\sqrt X\ell^2)\) proper-power log mass, or apply its prime-log version directly. References for the two standard ingredients: [Vaughan, An elementary method in prime number theory](https://bibliotekanauki.pl/articles/1393102.pdf) for the exponential-sum method; [The exceptional set of the Goldbach problem, §4](https://arxiv.org/html/2607.27282v2) states the Siegel–Walfisz and Vinogradov inputs and the classical unrestricted dyadic circle-method setup. The fixed summand grid here is the additional operation.

Writing \(\widehat{\mathbf1_{\mathfrak m}P_yP_{2X}}(N)\) for the minor contribution, Parseval gives
\[
\sum_{N\in\mathbb Z}|\widehat{\mathbf1_{\mathfrak m}P_yP_{2X}}(N)|^2
\le \sup_{\alpha\in\mathfrak m}|P_{2X}(\alpha)|^2 \int_0^1|P_y|^2
\ll_K X^3Q^{-1}\ell^9,
\tag{6}
\]
using \(\int|P_y|^2=\sum_{k\le y}w(k)^2\ll X\ell\). At each fixed \(y_i\), (6) excludes at most \(O_K(XQ^{-1}\ell^{2B+9})\) targets to achieve error \(X\ell^{-B}\). The union over \(2J+1=O(\ell^{B+1})\) prefixes has size \(O_K(XQ^{-1}\ell^{3B+10})\). Together with (5) and the chosen \(K\), this is \(O_{A,B}(X\ell^{-A})\). Outside the resulting set,
\[
C_{y_i}(N)= S(N)\min(y_i,N)+O_{A,B}(S(N)X\ell^{-B})
\]
simultaneously at every grid point. For any real \(y\in[0,2X]\), bracket \(y\) by adjacent \(y_i\)'s. The exact counts are monotone in \(y\) since \(w\ge0\), while the main term changes by at most \(S(N)X/J\) between adjacent points. The same bound therefore holds for every \(y\), allowed to depend on \(N\). Subtract the prefixes with \(y=aN,bN\) and account for at most two endpoint terms of size \(O(\ell^2)\). Division by \(N\) proves (1).

## 4. Consequences for the whole kernel and limitations

If actual prime-log correlation is replaced by the coprime von Mangoldt correlation of the old Li–Liu note, proper prime powers change the normalized count by at most \(O(X^{-1/2}\ell^3)\) uniformly in the window. A prime in a prime-pair representation which divides \(N\) must equal the other prime, so removing the possible diagonal changes it by another \(O(X^{-1}\ell^2)\). Thus (1) applies to the old arithmetic measure as well.

Central interval errors in (1) can be multiplied by the fixed smooth weight \(g(t)=\sqrt{t(1-t)}\) via Stieltjes partial summation: if an interval cumulative mass \(F(x)\) is bounded by \(D\) in modulus, weighted mass is at most \(D(\|g\|_\infty+\int|g'|)\). Closed endpoints use \(F(x)=\tau([a,x])\) and the usual endpoint Stieltjes identity, so the same uniform bound applies. The normalized central kernel satisfies
\[
|K_N(u,v)|=|\rho_N(u)\rho_N(v)\sigma_N([1-v,u])|
\ll_{A,B} S(N)\ell^{-B}
\]
on the triangle \(u+v\ge1\), and is zero elsewhere. The weights and the interval length are uniformly bounded, hence this is an HS bound and implies (2). The old unconditional pointwise upper sieve gives the all-even baseline \(\|T_N\|_{\rm HS}/S(N)\ll1\). Summing the square over good and exceptional targets, and choosing \(A,B\) arbitrarily large fixed, proves the normalized mean-square decay asserted above. If desired the unnormalized version follows by the elementary \(S(N)\ll\log(2N)\): up to constant the divisor product is bounded by \(\prod_{p\mid N}(1+1/p)\le\sum_{d\le N}1/d\), comparing Euler factors using a convergent \(O(1/p^2)\) factor.

No averaging argument here yields the signed error at an arbitrary exceptional target. In particular (6) legitimately uses a constant-in-\(N\) Fourier cutoff, but that same strength is insufficient to remove a sparse exceptional sequence. The [reflected random-pair obstruction](SignedMinorFourierObstruction.md) demonstrates this limitation for generic prime-supported weights with matching major, modulus, and \(X^3\log^{-A}X\)-scale averaged estimates. This note is a quantitative calibration of the Green–Tao-based qualitative result already in the repository, not a strengthening of the known exceptional-set bounds for the existence of some unrestricted prime pair. No claim of priority for these classical estimates or their moving-window implementation.
