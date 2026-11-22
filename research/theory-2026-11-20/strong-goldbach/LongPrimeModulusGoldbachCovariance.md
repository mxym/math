# Long prime moduli: a pointwise reflected-covariance test for Goldbach

For each fixed sufficiently large real \(B>0\), take genuine prime moduli near \(Q=N/(\log N)^B\). Their centered **reflected** progression covariance, normalized by the mass of the moduli, is equal to the actual central Goldbach count minus its Hardy–Littlewood principal term, up to a relative \(O(e^{-B})\) error on the principal term. The off-target aliases are evaluated by a ternary linear form with all three variables genuine primes. No primeness assumption on a hypothetical exceptional target is made. This is a pointwise necessary sign condition for a counterexample, **not** a bound on that sign.

## 1. Statement

Let \(N\to\infty\) run through even integers, put \(L=\log N\), and fix nonnegative \(w\in C_c^\infty(0,1)\) with
\[
 f(0)>0,\qquad f(v)=\int_{\mathbb R}w(t)w(1+v-t)\,dt.
\]
For example, \(w\) can be a symmetric nonzero central bump. Fix nonzero nonnegative \(g\in C_c^\infty(1,2)\), \(B>0\), \(Q=N/L^B\), and define
\[
 a_p=(\log p)w(p/N),\quad A=\sum_{p\ \rm prime}a_p,\quad
 R_w(N)=\sum_{p+p'=N\atop p,p'\ \rm prime}a_pa_{p'},
 \quad G_Q=\sum_{q\ \rm prime}(\log q)g(q/Q).
\]
All counts are ordered. For prime \(q\) in the support of \(g(q/Q)\) and \(a\in\mathbb F_q\), write
\[
 A_q(a)=\sum_{p\equiv a\bmod q}a_p,\qquad E_q(0)=0,\qquad E_q(a)=A_q(a)-\frac{A}{q-1}\quad(a\ne 0).
\]
For sufficiently large \(N\) (depending on \(B,w,g\)), any \(p\) with nonzero \(a_p\) exceeds \(2Q\). In particular \(A_q(0)=0\) and \(\sum_a E_q(a)=0\). Let
\[
 \Gamma_q(N)=\sum_{a\in\mathbb F_q}E_q(a)E_q(N-a),\qquad
 \mathfrak S(N)=\prod_p\frac{p(p-\nu_p(N))}{(p-1)^2},
 \quad \nu_p(N)=\begin{cases}1&p\mid N,\\2&p\nmid N.\end{cases}
\]
Then, with the order **fix \(B\), then let \(N\) tend to infinity**, uniformly in every even \(N\),
\[
 \boxed{\quad
  \frac1{G_Q}\sum_{q\ \rm prime}(\log q)g(q/Q)\Gamma_q(N)
  =R_w(N)-N\mathfrak S(N)f(0)
     +O_{w,g}(e^{-B}N\mathfrak S(N))+o_{B,w,g}(N).
 \quad}                                                         \tag{1}
\]
The constant in the displayed \(O(e^{-B})\) does not depend on \(B\). With any fixed \(\epsilon>0\) one can choose \(B\) once so that every sufficiently large hypothetical bad even target satisfies
\[
  \frac1{G_Q}\sum_q (\log q)g(q/Q)\Gamma_q(N)
       \le -(1-\epsilon)N\mathfrak S(N)f(0).                    \tag{2}
\]
Conversely, a uniform lower bound for the left side of (2) strictly above this threshold, for some such choice with the error smaller than the strict reserve, would give a genuine central prime pair for all sufficiently large even targets. No such bound is established here.

## 2. Ternary evaluation of the nonzero aliases

Put \(e(t)=\exp(2\pi it)\) and set
\[
 S(\alpha)=\sum_{p\ \rm prime}a_p e(\alpha p),\qquad
 U(\alpha)=\sum_{q\ \rm prime}(\log q)g(q/Q)e(\alpha q).
\]
For \(0<|h|\ll_w L^B\), the exact count for \(p+p'-hq=N\) is
\[
 T_h=\int_0^1 S(\alpha)^2 U(-h\alpha)e(-N\alpha)\,d\alpha.
\]
We prove uniformly, for any fixed \(K\),
\[
 T_h=NQ\,\mathfrak S_3(N,h)\int_0^\infty g(u)f(hQu/N)\,du
       +O_{B,K,w,g}(NQ L^{-K}),                                \tag{3}
\]
where
\[
 \mathfrak S_3(N,h)=\sum_{r\ge1}\frac{\mu(r)^2 c_r(N)c_r(h)}{\varphi(r)^3}
 =\prod_p\left(1+\frac{c_p(N)c_p(h)}{(p-1)^3}\right).           \tag{4}
\]
Here \(c_r(t)\) is the Ramanujan sum; the notation \(c_p(t)\) in (4) is **not** the Goldbach factor \(p(p-\nu_p)/(p-1)^2\).

For completeness, use arcs \(r\le L^C\), \((a,r)=1\), \(|\alpha-a/r|\le 2L^C/N\). They are disjoint for large \(N\). On the complement, Dirichlet approximation with denominator bound \(\lfloor N/L^C\rfloor\) gives a reduced approximant with \(L^C<r\le N/L^C\) and \(|\alpha-a/r|\le r^{-2}\). The classical Vinogradov–Vaughan bound for \(\sum_{n\le y}\Lambda(n)e(\alpha n)\), with terms \(y/\sqrt r+y^{4/5}+\sqrt{yr}\) and a fixed logarithmic loss, yields \(\sup_{\mathfrak m}|S|\ll_{w,D}N L^{-D}\) for arbitrarily prescribed fixed \(D\) by taking \(C\) large. Use partial summation on \(y\asymp_w N\) and remove prime powers at cost \(O(N^{1/2}L^2)\). One primary statement is [Bhowmik–Grimmelt, §4.3 Proposition 4.1](https://arxiv.org/html/2607.27282v2#S4.SS3); see also [their journal version](https://doi.org/10.1007/s10476-026-00191-z). Parseval gives \(\|S\|_2^2\ll_w NL\), \(\|U\|_2^2\ll_g QL\), and \(\|U(h\cdot)\|_2=\|U\|_2\) for every nonzero integer \(h\). Consequently the minor integral is \(\ll NQ L^{-D+1+B/2}\), not a binary pointwise minor estimate.

On the arc \(\alpha=a/r+\beta\), apply the Siegel–Walfisz prime-number theorem to both genuine prime sums, followed by summation by parts. All primes in either support exceed \(r\). Uniformly there, for every \(J>0\),
\[
 S(a/r+\beta)=\frac{\mu(r)}{\varphi(r)}V(\beta)+O_{B,C,J,w}(N L^{-J}),\qquad
 U(-h(a/r+\beta))=\frac{c_r(h)}{\varphi(r)}V_g(-h\beta)+O_{B,C,J,g}(Q L^{-J}),
\]
where \(V(\beta)=\int w(t/N)e(\beta t)\,dt\) and \(V_g(\beta)=\int g(t/Q)e(\beta t)\,dt\). The phase variation is \(O(L^C)\) on both supports since \(|h|Q\ll_w N\). Multiplication and total arc length \(O(L^{3C}/N)\) give the claimed arbitrary log reserve, by increasing \(J\). Summing \(e(-Na/r)\) over the reduced \(a\) yields \(c_r(N)\); the factor \(c_r(ha)=c_r(h)\) is independent of \(a\).

The series in (4) is absolutely convergent for every nonzero \(h\). Its tail beyond \(L^C\) is \(\ll L^{-C/2}\tau(|h|)^{O(1)}\): Rankin with exponent \(1/2\), nonzero primes outside \(h\) have local absolute terms at most \(1/(p-1)^2\), and the finitely many primes dividing \(h\) cost at most a fixed factor each. This is an arbitrary inverse-log reserve by increasing \(C\) in terms of \(B,K\). Extending the \(\beta\)-integral to \(\mathbb R\) costs an arbitrary log reserve using the rapidly decreasing \(V(\beta)\), trivial \(V_g\ll Q\), and the same coefficient sum. Exact Fourier inversion then gives
\[
 \int_{\mathbb R} V(\beta)^2V_g(-h\beta)e(-N\beta)\,d\beta
        =NQ\int_0^\infty g(u) f(hQu/N)\,du.
\]
This proves (3), for both signs of \(h\) and with the original modulus wavelength retained. In particular the parity factor is automatic, rather than discarded through replacing the prime modulus by an unrestricted integer.

## 3. The signed endpoint term

For an odd prime \(p\) write
\[
 s_p=\frac{p(p-\nu_p(N))}{(p-1)^2},\qquad
 d_p=\begin{cases}
 1-(p-1)^{-2}&p\mid N,\\
 1+(p-1)^{-3}&p\nmid N,
 \end{cases}\qquad D_N=\prod_{p\ge3}d_p.
\]
These are the local factors in (4) according as \(p\mid h\) or \(p\nmid h\). The factor at \(2\) is exactly \(2\mathbf 1_{2\mid h}\), since \(N\) is even. Let \(\lambda'_N\) be multiplicative, supported on odd squarefree integers, with \(\lambda'_N(p)=s_p/d_p-1\) for odd primes. Explicitly
\[
 \lambda'_N(p)=\begin{cases}1/(p-2)&p\mid N,\\-1/(p^2-3p+3)&p\nmid N.\end{cases}
\]
Then \(\mathfrak S_3(N,h)=2\mathbf 1_{2\mid h}D_N\sum_{d\mid h}\lambda'_N(d)\). The two Euler products have **different** normalizations:
\[
 D_N\sum_d\frac{\lambda'_N(d)}d=1,
 \qquad 2D_N\sum_d\lambda'_N(d)=\mathfrak S(N).                 \tag{5}
\]
The first follows from \((1-1/p)d_p+(1/p)s_p=1\) for every odd \(p\); in the second the factor 2 is the binary factor at 2. Absolute convergence holds for each \(N\).

We need a uniform relative error, not an absolute tail bound that silently assumes \(\mathfrak S(N)\) bounded. For \(\sigma=(\log L)^{-1}\le1/4\),
\[
 2D_N\sum_d |\lambda'_N(d)|d^\sigma\ll \mathfrak S(N).          \tag{6}
\]
Divide the left side by the second product in (5). At odd \(p\nmid N\), the product of ratios is uniformly bounded by convergence of \(\sum p^{-2+\sigma}\). At \(p\mid N\) the logarithm of the ratio is at most \((p^\sigma-1)/(p-2)\). For \(p\le L^2\) use \(p^\sigma-1\le e^2\sigma\log p\) and the Chebyshev bound \(\sum_{p\le L^2}(\log p)/(p-2)\ll\log L\). For \(p>L^2\), there are at most \(L/(2\log L)\) prime factors of \(N\); each factor contributes \(O(L^{-3/2})\). This proves (6) with an absolute constant.

Write \(F(v)=f(v)+f(-v)\) for \(v\ge0\), so \(F(0)=2f(0)\) and \(\int_0^\infty F(v)\,dv=(\int w)^2\). The elementary trapezoid rule with integrable second derivative gives, for all \(t>0\),
\[
 \sum_{k\ge1} F(kt)=\frac1t\int_0^\infty F(v)\,dv-\frac12 F(0)
        +O_w(\min(t,1)).
\]
For \(t>1\) this uses compact support. Taking \(t=2duQ/N\) after opening the divisor sum, using \(\min(t,1)\le t^\sigma\) and (5)–(6), gives uniformly for \(u\in[1,2]\),
\[
 \sum_{h\ge1}\mathfrak S_3(N,h)F(huQ/N)
   =\frac{N}{uQ}(\int w)^2 -\mathfrak S(N) f(0)
         +O_w(e^{-B}\mathfrak S(N)).                             \tag{7}
\]
Indeed \((2uQ/N)^\sigma\le4^{1/4}e^{-B}\). This explains why a rough error of order one in replacing the discrete \(h\)-sum by an integral would lose the entire required negative term. The sum on the left is actually finite for each \(u\).

## 4. Comparison with the actual centered prime-modulus sum

Let \(C_q(N)=\sum_{p+p'\equiv N\bmod q}a_pa_{p'}\). The exact congruence expansion has one \(h=0\) row contributing \(G_Q R_w(N)\), and every other \(h\) is in the range in (3). Summing first (3), with \(K>B+A\) for any required \(A\), and then (7) gives
\[
 \begin{split}
 \sum_{q\ \rm prime}(\log q)g(q/Q)C_q(N)
  ={}& G_Q R_w(N)+N^2(\int w)^2\int_0^\infty g(u)\frac{du}{u} \\
    &-NQ\mathfrak S(N) f(0)\int_0^\infty g(u)\,du
      +O_{w,g}(e^{-B}NQ\mathfrak S(N))+o_{B,w,g}(NQ).            \tag{8}
 \end{split}
\]
There is no unknown binary off-target error in this step; it has been replaced by (3). The local density on the original prime modulus is
\[
 v_N(q)=\frac{\#\{a\bmod q:a\ne0,\ N-a\ne0\}}{(q-1)^2}
       =\frac{q-\nu_q(N)}{(q-1)^2}=q^{-1}+O(q^{-2})
\]
uniformly whether or not \(q\mid N\). By the ordinary prime number theorem and smooth summation,
\[
  A^2\sum_{q\ \rm prime}(\log q)g(q/Q)v_N(q)
   =N^2(\int w)^2\int_0^\infty g(u)\frac{du}{u}+o_{B,w,g}(NQ).
\]
Here the \(O(q^{-2})\) correction costs \(O(N^2/Q)=o(NQ)\), and the arbitrary inverse-log PNT reserve is taken after fixing \(B\). Thus the large \(N^2\)-scale main term in (8) is exactly centered, not dropped by a qualitative convergence argument.

Expanding \(A_q(a)=A/(q-1)+E_q(a)\) on the units gives
\[
  C_q(N)-v_N(q)A^2=\Gamma_q(N)
  -\frac{2A}{q-1} E_q(N\bmod q)\mathbf 1_{q\nmid N}.
\]
The linear term disappears if \(q\mid N\). Otherwise its absolute value is \(\ll_{w}(N/q)(N/q+1)L\), since a residue class in the support contains \(O(N/q+1)\) integers. Aggregate \(\ll_B Q L^{2B+1}=o(NQ)\). Finally \(G_Q=Q\int g+O_{A,B,g}(Q L^{-A})\) by the ordinary PNT, and \(\mathfrak S(N)\ll\log\log(3N)\), or the weaker \(L^{O(1)}\), from the product. This proves (1), without renormalizing the exact \(G_Q R_w(N)\) coefficient. The positive universal lower bound for \(\mathfrak S(N)\) on even \(N\) follows from the factor 2 and convergence of \(\prod_{p>2}(1-(p-1)^{-2})>0\), so (2) follows after fixing \(B\) large enough.

## 5. Scope and comparison

The switch is a reflected, prime-modulus counterpart of Hooley's complementary divisor step for nonzero differences, as exposed in [Harper, *Simple Barban–Davenport–Halberstam type asymptotics for general sequences*, §3](https://wrap.warwick.ac.uk/id/eprint/192467/7/Journal%20of%20London%20Math%20Soc%20-%202025%20-%20Harper%20-%20Simple%20Barban%20Davenport%20Halberstam%20type%20asymptotics%20for%20general%20sequences.pdf). The latter uses differences and unrestricted integer moduli. We instead get true ternary prime conditions and the negative binary singular-series endpoint at a prescribed sum. [Goldston–Suriajaya, *On a smoothed average of the number of Goldbach representations*](https://arxiv.org/abs/2306.04807) uses the related progression pairing at target residue zero, not the same moving target/long-prime-modulus centered comparison. [Bhowmik–Grimmelt's 2026 analysis](https://arxiv.org/html/2607.27282v2#S7), [Pintz–Althöfer arXiv:2610.15559](https://arxiv.org/abs/2610.15559), and [Althöfer–Chen–Perelli–Pintz arXiv:2611.09386](https://arxiv.org/abs/2611.09386) use major-arc formulas and minor moments to constrain *sets* of targets (the sharper secondary exponents in the second paper are conditional as stated there), not to show this pointwise quadratic sign. The classical ternary estimate used here has no exceptional target set and no unproved spectral hypothesis.

The reflection \(a\mapsto N-a\) is an orthogonal involution on \(\mathbb R^{\mathbb F_q}\). With its even and odd projections \(E_q^\pm\), \(\Gamma_q=\|E_q^+\|_2^2-\|E_q^-\|_2^2\), not a nonnegative variance. Even imposing \(E_q(0)=0\), zero sum and positive raw AP counts does not give a sign: choose a two-element nonzero reflection orbit not involving 0, set its two errors to \(t,-t\) with \(0<t<A/(q-1)\), and the remaining errors to zero. Ordinary total variance bounds do not price the required signed difference. Formula (1) is thus a rigorous conditional detection criterion, not a proof of positivity, a construction of a bad target, or a general barrier to new prime-specific estimates.
