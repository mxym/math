# Exact asymmetric sieve kernel gives two smaller prime windows for squarefree P4

Written research note, 2026-11-24. This is a local prime-plus-squarefree-almost-prime result, not P3 or a proof of Goldbach. No priority claim.

## Theorem

Fix real \(0<a<b\). For every sufficiently large even \(N\), take either \(I=(aN^{.4832},bN^{.4832}]\), or \(I=(x,x+N^{.4916}]\) for **each** \(x\in[a\sqrt N,b\sqrt N]\). Set \(L=\log N\), \(Y=|I|\), \(X=\int_I du/\log u\), and
\[
 S_N=2\prod_{\ell>2}\left(1-(\ell-1)^{-2}\right)
          \prod_{\substack{\ell>2\\\ell\mid N}}\frac{\ell-1}{\ell-2},
 \qquad B=2XS_N/L.
\]
Uniformly throughout each family at least \((.005+o(1))B\) genuine primes \(p\in I\) have \(N-p\) squarefree, \(P^-(N-p)\ge N^{.0393}\), and \(\Omega(N-p)\le4\). Compared with the [earlier .49/.495 result](PrimeOppositeSubSquareRootShortP4.md), this improves the source location and the near-square-root window width, but uses a slightly weaker least-factor floor and a smaller certified count. The theorem here does not assert a planted profile at the new exponents.

## 1. Full evaluation of the actual switched Selberg denominator

For the actual large mark \(q\mid N-p\), write \(j=(N-p)/q\) and count it in the literal interval of length \(Y/q\). As in the parent proof, sift \(j\) below \(z=N^\mu\), and the true affine \(p=N-qj\) at primes up to \(K=z^v\), always with \(q>K>z\) in the range used below. For \(\ell<z\) there are two roots unless \(\ell\mid N\), when they coincide; for \(z\le\ell\le K\) there is one root. Define \(b_\ell=\nu_{\rm full}(\ell)/(\ell-\nu_{\rm full}(\ell))\) and \(c_\ell\) similarly for the actual asymmetric roots. Here \(\nu_{\rm full}(\ell)=2\) for \(\ell\nmid N\), otherwise \(1\). Put \(G_0(Q)=\sum_{d\le Q}\mu_{\rm M}(d)^2\prod_{\ell\mid d}b_\ell\), with \(\mu_{\rm M}\) the Möbius function. The [parent denominator computation](PrimeOppositeSubSquareRootShortP4.md) gives
\[
 G_0(Q)=\frac{(\log Q)^2}{2S_N}
      +O\!\left((1+\log Q)(\log\log N)^C\right),\qquad 1\le Q\le N.
\]
In fact, if \(e(d)\) are the coefficients of
\[
 \prod_{\substack{z\le\ell\le K\\\ell\nmid N}}
 \frac{1+c_\ell\ell^{-s}}{1+b_\ell\ell^{-s}},
\]
then the **exact finite convolution** is \(G_{\rm as}(K)=\sum_{d\le K}e(d)G_0(K/d)\). The local coefficients are \(1\) at \(1\) and \((c_\ell-b_\ell)(-b_\ell)^{j-1}\) at \(\ell^j\). At bounded \(v\) their total absolute mass through \(K\) is \(O(1)\): the sum of \(O(1/\ell)\) over \(z\le\ell\le K=z^v\) is \(O(1)\). The mass of terms containing a repeated prime and that arising from the \(O(\ell^{-2})\) correction in \(c_\ell-b_\ell=-1/\ell+O(\ell^{-2})\) are both \(O(1/z)\) by expanding the absolute products. Extending the approximate \(-1/\ell\) rule over \(\ell\mid N\) in this interval costs \(O(\log N/z)\). The convolved error of \(G_0\) is \(o((\log z)^2/S_N)\), uniformly for \(v\) on any fixed compact subinterval of \(v\ge1\), since \(S_N\ll(\log\log N)^C\).

The harmonic prime measure on \(u=\log\ell/\log z\) over \(1\le u\le v\) converges to \(du/u\) by Mertens, with repeated primes negligible. The quadratic part above is continuous across the boundary \(\sum u_i=v\). The finite convolution integrals converge uniformly in \(v\) on compact intervals, by subdivision in \(u_i\) and uniform continuity of the positive-part quadratic. Consequently
\[
 G_{\rm as}(K)=\frac{(\log z)^2}{S_N}(J(v)+o(1)),\qquad
 J(v)=\frac12\sum_{j\ge0}\frac{(-1)^j}{j!}
     \int_{\substack{u_i\ge1\\\sum u_i\le v}}(v-\textstyle\sum u_i)^2\prod_i\frac{du_i}{u_i}.
\]
The \(j=0\) contribution is \(v^2/2\); the other sum is finite at each \(v\). In particular this includes the higher-order overlapping local losses rather than bounding all of them by a single subtraction.

For \(s>0\) the Laplace transform is
\[
 \widehat J(s)=s^{-3}\exp\!\left(-\int_1^\infty e^{-su}\,\frac{du}{u}\right)
\]
by convolution of the damped absolutely integrable series. It obeys
\(-\frac d{ds}(s\widehat J)=(2-e^{-s})\widehat J\). With \(J=0\) for \(v\le0\), this yields
\[
 vJ'(v)=2J(v)-J(v-1),\quad J(v)=v^2/2\ (0\le v\le1),
 \qquad (J(v)/v^2)'=-J(v-1)/v^3 .
\]
The derivative is continuous for \(v>0\). A first zero of \(J'\) after \(1\) would have \(0\le J(v-1)\le J(v)\), \(J(v)>0\), so the displayed equation gives \(J'(v)>0\), a contradiction. Thus \(J\) increases on \(v>0\).

## 2. Genuine source distribution and the signed Richert margin

Let \(\theta\) denote the size exponent of \(p\), and \(\rho\) its interval length exponent: \((\theta,\rho)=(.4832,.4832)\) or \((.5,.4916)\). In both cases take
\[
 d_0=.24159,\quad \mu=.0393,\quad \beta=.3135,\quad T=.2143,\quad
 D=N^{d_0},\quad \eta=5-1/\beta,\quad K=N^{(\rho-t)/2-.00001}
\]
for a marked prime \(q=N^t>N^T\). Then \(q>K>z\), and \(2<v=(\rho-t-.00002)/(2\mu)<4\) for \(T<t<\beta\).
The true source level for the first window is \(N^{.2416}\) minus logarithms by ordinary Bombieri–Vinogradov. In the second use [Perelli–Pintz–Salerno, p. 530, Theorem and (2)–(3)](https://www.numdam.org/article/ASNSP_1984_4_11_4_529_0.pdf) at source scale \(P=x+Y\asymp\sqrt N\), with maximum length \(P^{.98319}\) and modulus ceiling \(P^{.48319}\) minus logarithms. Divide each required segment of length at most \(Y\) into at most \(1+Y/P^{.98319}\) pieces, each starting in \([P/2,P]\). This gives arbitrary logarithmic savings relative to the actual length parameter \(Y\), while the true modulus ceiling has \(N\)-exponent .241595, strictly exceeding .24159. Removing Mangoldt prime powers across all tested moduli costs \(O(D P^{1/2}L^C)\), strictly below \(Y L^{-A}\) for any fixed \(A\): its exponent is .48319 in the first window and .49159 in the second. Partial summation and fixed divisor weights are handled as in the parent proof.

Use the same genuine base sieve and Richert score as in that proof. In units \(B\), the base lower coefficient is \(g_*(d_0/\mu)/d_0\), and the small marked-prime debit before the factor \(1/\eta\) is at most
\[
 C_1=\int_\mu^T
   \frac{1-t/\beta}{t(d_0-t)} h_*\!\left(\max(2,(d_0-t)/\mu)\right)dt .
\]
These are the standard linear sieve \(g_*(s)=sf(s)/(2e^\gamma)\), \(h_*(s)=sF(s)/(2e^\gamma)\). The conditional small-mark sieve uses the actual modulus \(qd\le D\) and cutoff \(\min(z,\sqrt{D/q})\). As before, each such test has at most one named \(q\ge z\), so its residual is not counted twice. After deleting source primes dividing \(N\), all the congruence classes with positive density are reduced.

For a large mark, the actual affine bound is \(Y/(qG_{\rm as}(K))+O(K^2L^C)\), with the finite square coefficients and floors from the parent proof. The floor sum is \(O(N^{\rho-.00002}L^C)=o(B)\); no distribution of primes in \(j\) is assumed. Since \(X\sim Y/(\theta L)\) uniformly in each source window, the coefficient in units \(B/q\) is at most \(\theta/(2\mu^2J(v))+o(1)\). The long-mark debit is therefore at most
\[
 C_2(\theta,\rho)=\int_T^\beta
   \frac{(1-t/\beta)\theta}{2t\mu^2J((\rho-t-.00002)/(2\mu))}\,dt .
\]
The squareful-complement cleanup is \(O(Y/z+YN^{-1/3}+N^{1/3})=o(B)\) by summing square divisors up to \(N^{1/3}\) and switching \(N-p=c r^2\) above it, as in the parent proof. On the real squarefree rough complements the Richert weight is at most 1 and is nonpositive when \(\Omega(N-p)\ge5\), since the mark sum is at least \(\Omega(N-p)-1/\beta\). Thus a positive normalized signed margin gives the asserted unweighted count.

## 3. Directed proof of positivity

The [standalone BigInt replay](check_exact_asymmetric_p4_windows.js) encloses the normalized sieve coefficient via its delay equations and the switched kernel via the equation for \(J(v)/v^2\). On each mesh cell, bound the delayed nonnegative numerator by \(J\) at the two opposite endpoints, and use the denominator endpoints in the favorable direction. The decreasing weight \((1-t/\beta)/t\), monotonicity of \(J\), and the exact endpoint enclosures give directed upper Riemann sums for both mark debits. The resulting values are
\[
 g_*(d_0/\mu)\ge1.725583443877592,\qquad C_1\le10.0884304862,
\]
and \(C_2\le2.8276566986\) in the first window and \(C_2\le2.7755190003\) in the second. In both cases \(g_*(d_0/\mu)/d_0-(C_1+C_2)/\eta>.005\), with certified margins at least .0074 and .0362, respectively. Every arithmetic comparison in the replay is exact.

The full asymmetric denominator is still bounded above by the full two-root denominator, term by term at the level of the defining nonnegative coefficients. Improving the local constant here therefore does not resolve the [separate middle-moment problem for P3](PrimeOppositeSquareRootP3Target.md).
