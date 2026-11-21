# Exact smooth δ coverage of one binary Goldbach target: unconditional removal of the linear terms

Let \(N=X\) be a large even integer, \(L=\log X\); write \(e(t)=e^{2\pi i t}\). Fix nonnegative smooth weights \(w,g\), with compact supports in \((.30,.37),(.60,.74)\), respectively, \(w\) not identically zero, and \(g=1\) near \(1-\operatorname{supp}w\). The weighted prime-pair count is
\[
 R_w(N)=\sum_{p+p'=N}(\log p)(\log p')w(p/X)g(p'/X).
\]
For every fixed \(A>0\), take a fixed sufficiently large \(B=B(A)\), and \(Q=\sqrt X/L^B\). We give an exact decomposition into \(q\le Q\) complete rational numerator blocks. Their pole–pole terms contribute \(X\mathfrak S(N)\int w+O(X^{.81})\), and the **sum of the absolute values over all moduli** of either pole–error block is \(O_A(X/L^A)\). There is no character zero hypothesis. The remaining centered–centered blocks retain the full target phase; their sum is not evaluated. This is an elementary application of Heath-Brown's δ symbol and the Bombieri–Vinogradov theorem, not a new estimate for primes in progressions.

## Exact physical kernel

Choose \(\omega\in C_c^\infty((1/2,1))\), nonnegative of integral one; take even \(\psi\in C_c^\infty((-1/2,1/2))\) equal to one near zero. Set \(c_Q=Q/\sum_{j\ge1}\omega(j/Q)=1+O_D(Q^{-D})\), and
\[
 h(x,y)=\sum_{j\ge1}\frac{\omega(xj)-\omega(|y|/(xj))}{xj},\qquad
 b_x(v)=x h(x,xv)\psi(xv),\quad H=qQ,\quad x=q/Q.
\]
With \(c_q(k)=\sum_{a(q)}^*e(ak/q)\), one has **exactly**, for every integer \(k\),
\[
 1_{k=0}=c_Q\sum_{q\le Q}H^{-1} c_q(k)b_{q/Q}(k/H).\tag{1}
\]
Indeed without the common cutoff \(\psi(k/Q^2)\), collect terms with \(d=qj\) and use \(\sum_{q|d}c_q(k)=d1_{d|k}\). For \(k\ne0\) the result divided by \(c_Q\) is \(Q^{-1}\sum_{d|k}[\omega(d/Q)-\omega(|k|/(dQ))]=0\) by exchanging complementary divisors. For \(k=0\) it is \(1/c_Q\). Restoring the cutoff preserves both identities, and forces \(q<Q\) in either of the two \(\omega\) terms. This is the [D. R. Heath-Brown smooth δ symbol, Theorem 1 (1996)](https://doi.org/10.1515/crll.1996.481.149), with a harmless physical cutoff.

The functions \(b_x\), \(0<x\le1\), have uniformly bounded Schwartz seminorms and \(\int b_x=1+O_D(x^D)\). For details put \(C=\int\omega(t)dt/t, C_x=\sum_j\omega(xj)/j, S(t)=\sum_j\omega(t/j)/j\). Then \(b_x(v)=(C_x-S(|v|))\psi(xv)\); Poisson summation on the smooth compactly supported Riemann sums gives \(C_x=C+O_D(x^D)\), \(S(t)=C+O_D(t^{-D})\) for \(t\ge1\) (use the function \(u\mapsto \omega(1/u)/u\) on \(u=j/t\)). The same rapid decay holds for every positive derivative of \(S(t)\), by differentiated Poisson summation. Thus \(b_x\) differs from \(b_0(v)=C-S(|v|)\) in any specified weighted norm by \(O_D(x^D)\). Its limiting mass is one: for \(V>0\),
\(\int_0^V(C-S(v))dv=\int\omega(t)\{V/t\}dt\to 1/2\), by period averaging after \(s=1/t\). Double by evenness.

## Sector decomposition, with no square-root factorization needed

Let \(d\theta_i(y)=\sum_p(\log p)w_i(p/X)\delta_p(dy)\) for \((w_1,w_2)=(w,g)\). For unit \(a\bmod q\) set the complex prime measure \(P_{i,a}(dy)=e(-ay/q)d\theta_i(y)\) and its principal replacement \(J_i(dy)=\mu(q)w_i(y/X)dy/\varphi(q)\). This is precisely the pole term since the mean of \(e(-ar/q)\) over reduced residues \(r\) is \(\mu(q)/\varphi(q)\); all prime supports exceed \(q\). Set \(E_{i,a}=P_{i,a}-J_i\). Integrate each ordered pair of measures against
\(
 c_Q H^{-1} b_{q/Q}((y+z-N)/H)
\)
and take the complete sum over \(a(q)^*\) with coefficient \(e(aN/q)\). Denote the resulting four real blocks by \(M_q,L_{1q},L_{2q},D_q\) for \((J,J),(E,J),(J,E),(E,E)\). Conjugate numerators pair. Formula (1), with even \(b_x\), gives exactly
\[
 R_w(N)=\sum_{q\le Q}(M_q+L_{1q}+L_{2q}+D_q).\tag{2}
\]
There is no approximation by disjoint arcs, nearest-rational assignment, or exceptional target set. \(D_q\) uses two actual centered fluctuations, not two principal characters.

Write \(s_q=\mu(q)^2 c_q(N)/\varphi(q)^2\). The unmodulated pole integral multiplying \(c_Qs_q\) is \(O(X)\) for every \(q\) and equals \(X\int w+O_D(H+X(q/Q)^D)\) for \(q\le\sqrt Q\). This follows by substituting \(z=N-y+Hv\), using uniform first absolute moments, \(g(1-y/X)=1\) on \(w\), and the mass formula. The usual prime product gives \(\mathfrak S(N)=\sum s_q=2\prod_{p>2}(1-1/(p-1)^2)\prod_{p|N,p>2}(p-1)/(p-2)\), bounded below by a positive constant. For fixed \(0<\kappa<1\), \(\sum_q |s_q|q^\kappa\ll_{\kappa}X^{o(1)}\): the product away from \(p|N\) converges; at \(p|N\) it is at most \(\prod_{p|N}(1+O(p^{-1+\kappa}))=X^{o(1)}\) (split off finitely many primes, or use \(\omega(N)\ll L/\log L\)). Taking \(\kappa=.9\) and truncating at \(\sqrt Q=X^{1/4-o(1)}\) bounds both large-modulus tails by \(X^{.775+o(1)}\); the short-modulus archimedean error is \(X^{.75+o(1)}\). This proves the asserted model error.

## Absolute removal of both mixed families

For \(L_{1q}\) introduce the long test
\[
 f_q(u)= w(u)\int b_{q/Q}(v)g(1-u+(H/X)v)dv.
\]
Every derivative of \(f_q\) is bounded uniformly by moving it to \(w,g\) and using uniform kernel \(L^1\); the support is fixed. The mixed term is \(c_Q\mu(q)/\varphi(q)\) times the discrepancy of \(\sum_p(\log p) f_q(p/X)c_q(N-p)\) from its reduced-residue principal model. Expand \(c_q(k)=\sum_{d|(q,k)}d\mu(q/d)\). For \((d,N)>1\) no prime in the support is \(N\bmod d\): it would divide \(d\le Q\). Nor can a reduced residue of \(q\) lie there. For \((d,N)=1\) precisely \(\varphi(q)/\varphi(d)\) reduced residues lift \(N\bmod d\). Thus (including arbitrarily nonsquarefree moduli)
\[
 L_{1q}=\frac{c_Q\mu(q)}{\varphi(q)}\sum_{\substack{d|q\\(d,N)=1}} d\mu(q/d)
 \left[\sum_{p\equiv N(d)}(\log p) f_q(p/X)-\frac{X}{\varphi(d)}\int f_q\right].\tag{3}
\]
For the other mixed term exchange \(w,g\). Each bracket is \(\ll\max_{a(d)^*}\max_{t\le 2X}|\theta(t;d,a)-t/\varphi(d)|\) by partial summation; no dependence on \(q\) or derivative loss. Also \(\sum_{q\le Q:d|q}d/\varphi(q)\ll L\log\log X\) by \(q/\varphi(q)\ll\log\log(3q)\). The classical maximal Bombieri–Vinogradov theorem, with its exponent chosen to absorb these logarithms, proves \(\sum_q(|L_{1q}|+|L_{2q}|)\ll_A X/L^A\). The von Mangoldt formulation implies this prime version since each modulus incurs at most \(O(\sqrt X\log^2 X)\) for proper powers and \(B\) can be increased. See E. Bombieri, *On the large sieve*, Mathematika 12 (1965), 201–225; H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 17.

In particular a target missing from the support has \(\sum_{q\le Q}D_q=-X\mathfrak S(N)\int w+O_A(X/L^A)\). This does not show such a target exists, nor establish aggregate cancellation of the quadratic terms.

For a comparison of exact quantities, [Bhowmik–Grimmelt's 2026 major-arc formula](https://doi.org/10.1007/s10476-026-00191-z) treats ordinary circle-method major arcs, including nonprincipal zero terms. Equation (2) here instead covers the full individual target by a smooth delta identity; the entire centered–centered contribution stays in the formula and is not bounded by (3). No novelty for the delta identity or the distribution theorem is asserted.
