# A fixed-angle two-large-factor exclusion on a true prime-opposite cloud

Research note, 2026-11-24. No target factorization hypothesis is required, except that \(N\) is even. The statement concerns a positive subfamily of true prime-opposite rows, not macroscopic analytic reserve and not a proof of a Goldbach pair.

**Theorem.** Fix \(1/3<\rho\le1/2\), \(0<\alpha<\beta<1\), and \(0<\mu<\rho/4\). There are \(\delta=\delta(\rho,\mu,\alpha,\beta)>0\) and \(c>0\) such that for every sufficiently large even \(N\), at least
\[
 c\,F_N(N^\mu)\frac{N^\rho}{(\log N)^2},\qquad
 F_N(t)=\prod_{\substack{3\le \ell\le t,\ \ell\mid N\\ \ell\ {\rm prime}}}
                 \frac{\ell-1}{\ell-2},
\]
distinct true primes \(p\in(\alpha N^\rho,\beta N^\rho]\), \((p,N)=1\), satisfy both: (i) \(N-p\) has no prime divisor at most \(N^\mu\); (ii) \(N-p\) has **at most one prime factor exceeding \(N^{1/2-\delta}\), counted with multiplicity**. In particular \(\delta\) is fixed rather than a vanishing logarithmic window. At a hypothetical no-prime-pair target these are real composite first-step rows. Even when there are some Goldbach pairs the displayed assertion is true, and primes \(N-p\) are allowed in the good subfamily.

Let \(H=N^\rho\), \(L=\log N\), and \(z_0=N^\mu\).

## 1. Genuine rough prime-source lower bound (uniform in \(N\))

Sieve the literal sequence \(N-p\) for primes \(p\in I=(\alpha H,\beta H]\), with sifting primes \(\ell\le z_0\) that do not divide \(N\). Every squarefree divisor \(d\) built from these primes tests the actual reduced prime progression \(p=N\bmod d\) and has main density \(g_0(d)=1/\varphi(d)\). Bombieri–Vinogradov at both endpoints of \(I\), with its maximum over reduced residue classes, gives \(\sum_{d\le N^\xi}|r_d|\ll_A H/L^A\) for any fixed \(\xi<\rho/2\). We take \(2\mu<\xi<\rho/2\) and a fixed \(2<s_0<\min(3,\xi/\mu)\); hence a genuine level \(z_0^{s_0}\le N^\xi\) is sufficient. The dimension-one lower linear sieve gives a positive \(f(s_0)=2e^\gamma\log(s_0-1)/s_0\). Its dimension-one product condition is uniform because \(2\mid N\) is excluded and omitting primes only improves the upper condition \(\prod(1-g_0(\ell))^{-1}\) on subintervals. The exact main local product is
\[
 V_N(z_0)=\prod_{\substack{3\le\ell\le z_0\\\ell\nmid N}}
                \left(1-\frac1{\ell-1}\right)
 \asymp \frac{F_N(z_0)}{\log z_0}
\]
with absolute comparability by Mertens and the convergent local correction. The base prime mass is \(\operatorname{Li}(\beta H)-\operatorname{Li}(\alpha H)\asymp H/L\). Delete the at most \(\omega(N)=O(L)\) source primes dividing \(N\) only after sifting. For the remaining sources no factor of \(N\) can divide their opposite. Thus there is a \(c_0>0\), depending only on the fixed parameters, with at least \(c_0 F_N(z_0)H/L^2\) genuine rough prime sources for all sufficiently large \(N\). References: [Bombieri, *On the large sieve*](https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/S0025579300005313); [the linear sieve in *Weighted sieves with switching*, Lemma 2.5](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C). This is ordinary prime distribution at scale \(H\), not a short interval for primes at scale \(N\).

## 2. Reduction of bad rough rows to a thin hyperbolic band

Take a small \(\delta>0\) with \(2\delta<\mu\), to be specified later. If a rough row has two prime factors \(q\le r\) above \(N^{1/2-\delta}\), their product divides \(N-p\). The quotient \(b=(N-p)/(qr)<N^{2\delta}<z_0\). If \(b>1\) it would supply a sifting prime divisor, impossible. Thus \(N-p=qr\), and \(q<\sqrt N\). This argument permits \(q=r\) if multiplicity provides two factors.

Cover the range \(N^{1/2-\delta}<q\le\sqrt N\) by at most \(1+\delta L/\log 2\) adjacent dyadic shells of the form \(q\in J\subset[Q,2Q]\), where \(N^{1/2-\delta}\le Q\le \sqrt N\). We count true prime triples \(q,r,p=N-qr\) in each shell. The upper bound below enlarges the region by dropping any ordering or extra cutoff on \(r\). The enlarged \(r\) is still \(\asymp N/Q\), so \(p,q,r\) in a prime triple are all larger than the small upper-sieve primes when \(N\) is large.

## 3. Per-residue thin-band count, including both endpoint errors

For integer \(p\in I\), replace the endpoints by half-integers \(A=\lfloor\alpha H\rfloor+1/2,\ B=\lfloor\beta H\rfloor+1/2\), so exactly \(A<p<B\). The band of lattice points is
\[
 q\in J,\qquad (N-B)/q<r<(N-A)/q.
\]
There is no equality at either real boundary for integer \(q,r\). Its real area is \(\mathcal V=(B-A)\int_J dq/q\ll H\), independently of the shell size and \(\delta\). Let \(d\le D\), with \(D=N^\lambda\) for a fixed sufficiently small \(\lambda>0\) chosen below. For arbitrary residues \(a,b\bmod d\), put \(q=a+dj,\ r=b+dk\). For each allowable integer \(j\), the \(k\)-interval is between the two functions
\[
 f_c(j)=\frac{N-c}{d(a+dj)}-\frac b d,\qquad c=A,B.
\]
Its endpoint functions never take exact integer values on these samples, since \(N-c\) is a half-integer and \(q,r\) would be integral. The count therefore equals the sum of the interval lengths plus a difference of the two ordinary sawtooth sums. The length can be less than 1; this is an equality of floor differences with a sawtooth correction, not an assumption of having one point in every interval. The main length sum is
\[
 \frac{B-A}{d}\sum_{\substack{q\in J\\q\equiv a\bmod d}}\frac1q
 = \frac{\mathcal V}{d^2}+O(H/(dQ)).
\]
This follows by comparing the monotone function \(1/q\) in one progression with its integral; the error for the original sum is \(O(1/Q)\), including the possibly incomplete endpoints of the progression. It is independent of \((a,d)\).

For either endpoint, \(f_c''(j)=2d(N-c)/(a+dj)^3\asymp dN/Q^3\) on this shell, with absolute comparability since \(c=O(\sqrt N)\). The number of samples is \(O(Q/d)\) since \(d\ll Q\); an empty interval is trivial. For frequency \(h\ge1\), van der Corput's second derivative estimate for the real phase \(h f_c\) gives
\[
 \left|\sum_j e(h f_c(j))\right|
 \ll \frac{\sqrt N\,\sqrt h}{\sqrt{Qd}}
       + \frac{Q^{3/2}}{\sqrt N\,\sqrt{hd}},
 \qquad e(t)=e^{2\pi i t}.
\]
There is **no** coprimality condition on \(h,a,b,d\) in a second derivative estimate: it uses the actual real derivative of the phase, and \(b/d\) is only an additive constant. The discrepancy inequality of Erdős–Turán with Fourier cutoff \(M=\lfloor N^{1/6}\rfloor\) bounds each sawtooth sum by
\[
 \ll \frac{Q}{dM}
     +\frac{\sqrt N\,\sqrt M}{\sqrt{Qd}}
     +\frac{Q^{3/2}}{\sqrt{Nd}}
 \ll N^{1/3+\delta/2}.
\]
The bound for a sawtooth follows by integrating the discrepancy of fractional parts on intervals \([0,t)\), since \(u\mapsto u-1/2\) has bounded variation. No endpoint residue or interval whose length is shorter than 1 is left uncounted. The cited standard estimates are [Graham–Kolesnik, *Van der Corput's Method of Exponential Sums*, Theorem 2.2](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf) and [Erdős–Turán, 1948](https://users.renyi.hu/~p_erdos/1948-03.pdf).

Consequently in **each** of the \(d^2\) residue pairs the count is
\[
 \mathcal V/d^2+O(N^{1/3+\delta/2}).
\]
The main term is independent of the residues, and \(H/(dQ)\) is absorbed since \(\rho\le1/2\) and \(\delta\) is small. For later uniformity fix once and for all \(\delta_0>0\) small and \(\lambda>0\) with
\[
 1/3+\delta_0/2+2\lambda<\rho,\qquad
 \lambda<1/100,\quad \delta_0<1/100 .
\]
All displayed estimate constants then hold for every \(0<\delta\le\delta_0\) with the same \(\lambda\).

## 4. Uniform dimension-three upper sieve on the genuine band

For prime \(\ell\), let \(\rho_N(\ell)\) count residue pairs with \(\ell\mid q r(N-qr)\). The two axes give \(2\ell-1\) pairs. If \(\ell\nmid N\) the nonzero solutions to \(qr=N\) add \(\ell-1\) others. If \(\ell\mid N\), they add none. Thus
\[
 \rho_N(\ell)=
 \begin{cases}3\ell-2,&\ell\nmid N,\\2\ell-1,&\ell\mid N,\end{cases}
 \qquad g(\ell)=\rho_N(\ell)/\ell^2.
\]
For squarefree \(l\le D\), CRT and the per-residue count give
\[
 \#\{(q,r)\text{ in band}:l\mid q r(N-qr)\}
   =\mathcal V\,g(l)+O\big(N^{1/3+\delta/2}\rho_N(l)\big),
\]
where both functions extend multiplicatively to squarefree moduli, and \(\rho_N(l)\le l\,3^{\omega(l)}\). In particular (the case \(\ell=2\) uses \(2\mid N\)) \(0<g(\ell)<1\) and \((1-g(\ell))^{-1}\le 5\).

For clarity the needed Selberg bound can be seen directly. For \(Z=N^{\lambda/2}\) use signed weights supported on squarefree \(d\le Z\), with \(\lambda_1=1\). Square the divisor sum \(\sum_{d\mid q r(N-qr)}\lambda_d\); it is at least 1 on every triple of actual primes \(q,r,p>Z\). For \(w_r=\prod_{\ell\mid r}(g(\ell)^{-1}-1)\) and \(u_r=\sum_{d:r\mid d}\lambda_d g(d)\), the quadratic main coefficient is
\[
 \sum_{d,e}\lambda_d\lambda_e g([d,e])=\sum_{r\le Z}w_r u_r^2.
\]
This follows by expanding \(g([d,e])=g(d)g(e)\sum_{r\mid(d,e)}w_r\). Divisibility inversion gives \(\sum_r\mu(r)u_r=1\). Take \(u_r=\mu(r)/(w_r G)\), where \(G=\sum_{r\le Z}\mu(r)^2/w_r\), and invert. The main coefficient is \(1/G\); the inverted weights satisfy \(|\lambda_d|\le\prod_{\ell\mid d}(1-g(\ell))^{-1}\le5^{\omega(d)}\), since
\[
 |\lambda_d|=\frac{1}{g(d)w_dG}
            \sum_{\substack{m\le Z/d\\(m,d)=1}}
                         \frac{\mu(m)^2}{w_m}.
\]
All sums indexed by \(w_r\) are on squarefree integers; the factors for 1 are 1. Summing errors by \(l=[d,e]\le Z^2=D\), each \(l\) has at most \(3^{\omega(l)}\) ordered pairs \((d,e)\). The total error is
\[
 \ll N^{1/3+\delta/2}\sum_{l\le D} l\,C^{\omega(l)}
 \ll_\epsilon N^{1/3+\delta_0/2}D^{2+\epsilon}
 \ll N^{\rho-\kappa_0}
\]
for some fixed \(\kappa_0>0\), taking the auxiliary \(\epsilon>0\) small. The elementary \(C^{\omega(l)}\ll_\epsilon l^\epsilon\) for fixed \(C\) follows by separating the finitely many small primes at which \(C>\ell^\epsilon\).

For the main term let \(y=Z^\nu\) with a sufficiently small fixed \(\nu>0\) and \(y\le z_0\) (choose \(\nu\lambda/2\le\mu\)). On all squarefree divisors of \(\prod_{\ell\le y}\ell\), assign weights \(1/w_r\). Their total is \(P_y=\prod_{\ell\le y}(1-g(\ell))^{-1}\), and their weighted mean of \(\log r\) after dividing by \(P_y\) is \(\sum_{\ell\le y}g(\ell)\log\ell\ll\log y\), since \(g(\ell)\le3/\ell\). Choose \(\nu\) so this mean is at most \((\log Z)/2\); at least half the weight then has \(r\le Z\), so \(G\ge P_y/2\).

For odd \(\ell\nmid N\), \(1-g(\ell)=(1-1/\ell)(1-2/\ell)\), with its product comparable to \((\log y)^{-3}\) when using this formula at all odd primes. For odd \(\ell\mid N\) the actual value is \((1-1/\ell)^2\), which changes the former expression by the **exact** ratio \((\ell-1)/(\ell-2)\). The factor at 2 is a fixed \(1/4\). Hence
\[
 1/G\ll \prod_{\ell\le y}(1-g(\ell))
       \ll F_N(y)/(\log y)^3\ll F_N(z_0)/L^3 .
\]
The equality of the dividing-prime ratio here with the lower-sieve ratio is essential for arbitrary even \(N\). Replacing \(y\) by \(z_0\) only in \(F_N\) uses its monotonicity; \(\log y=(\nu\lambda/2)L\) with a fixed positive coefficient. Thus no moving radical loss, hidden factor in \(\delta\), or unproved independence assumption is used.

It follows that each shell contains at most
\[
 C\,F_N(z_0) H/L^3+O(N^{\rho-\kappa_0})
\]
actual prime triples. The fixed constants may depend on \(\rho,\mu,\alpha,\beta,\lambda,\nu,\delta_0\), but not on \(N\) or the final \(0<\delta\le\delta_0\).

## 5. Match and conclude

Sum the shell bounds. Since there are at most \(1+\delta L/\log2\), each bad rough source counted in section 2 belongs to the resulting prime triple set. Its source need not be counted exactly once for this upper bound. Thus the number of bad rough roots is at most
\[
 C_1\delta\,F_N(z_0)H/L^2+o(F_N(z_0)H/L^2)
\]
with \(C_1\) independent of the final \(\delta\). The total power error remains negligible after at most \(O(L)\) shells, and \(F_N(z_0)\ge1\). Choose \(0<\delta<\min(\delta_0,\mu/2,c_0/(2C_1))\). Subtracting from the genuine rough lower bound gives the asserted positive many real first rows.

This excludes a fixed angular simultaneous large-factor type without planting mass into \(N-p\) or demanding \(N\) be dyadic/small radical. It does not assert there is any prime factor above \(N^{1/2-\delta}\), exclude two distinctly smaller factors, or decide whether any complement is prime. The present exponential-sum test uses the \(N^{1/3}\) thin-band discrepancy, so this proof does not reach roots of scale \(N^\rho\) with \(\rho\le1/3\), let alone fixed or polylogarithmic roots. It also does not automatically transfer the count to a different central analytic chamber.

The sieve and discrepancy inputs are classical. No priority claim is made for this application.
