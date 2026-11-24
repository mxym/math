# A polynomial band of true balanced semiprime denominators for the G23 mixed statistic

Research note, 2026-11-24. This proves a new composite-denominator region, not a repetition of [the good-prime band](SmallRadicalGoodPrimeDenominatorArcs.md). In particular it does not cover arbitrary composite denominators, the exceptional products removed below, or the unresolved dense coprime slope correlation.

## 1. Statement

Use \(P\) large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=PJ\) fixed interior, \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\), and \(R_w(n)=1_{P^-(n)>w}\). The short marker is \(s(n)=\sum_{p\in\mathcal P,\ p\mid n}1\) for any subset \(\mathcal P\) of actual primes in \((P^\sigma,D]\), \(0<\sigma<1/4\), \(D=P^{1/2}e^{-L^{3/5}}\). The actual unmarked Fourier coefficients are
\[
f(n)=1_{n\in I}(\log n)s(n)R_z(n)\lambda(n),\qquad
g(m)=1_{m\in P-I}R_y(m)\lambda(m).
\]
As usual \(S_f(\alpha)=\sum_n f(n)e(n\alpha)\) and \(S_g\) similarly. For sufficiently small fixed \(\eta>0\) put \(Q=P^\eta\). Consider **unordered distinct true prime factors** \(a,b\in[Q,2Q]\), and \(q=ab\), so \(\operatorname{rad}(q)=q\asymp P^{2\eta}\).

All but \(O(P^{1.4\eta})\) such products are good, in the precise sense below. For any fixed \(J_0>0\), let \(\mathfrak B_2\) be the union over all good products and all their reduced numerators \(c\) of the arcs
\[
\alpha=c/q+\beta,\qquad |\beta|P\le L^{J_0},\quad(c,q)=1.
\]
Then, for every \(A>0\), the actual unmarked product satisfies
\[
\int_{\mathfrak B_2}|S_f(\alpha)S_g(\alpha)|\,d\alpha=O_A(PL^{-A}).
\tag{1}
\]
There are \(\asymp Q^2/L^2\) good products by PNT and unique prime factorization. Their full reduced arcs have measure \(\asymp Q^4 L^{J_0-2}/P\), since \(\varphi(q)\asymp Q^2\) and denominators \(\ll Q^2\) have disjoint arcs of these widths for small fixed \(\eta\). They are ordinary minor arcs and have large radical. If the exact translated selector with \(M\ge800\) offsets is retained on \(f\), their actual absolute frequency bill is \(o(PV_y(P)/L)\) using the precise selector deletion in §5.

## 2. Good products and a uniform primitive power bound

Take \(\kappa=1/1000\) and \(T=P^{100\eta}\). A conductor \(f_0\) is bad if any primitive character of that conductor has a zero in \(\Re s\ge1-\kappa,\ |\Im s|\le2T+1\). A product \(q=ab\) is good if \(a,b,ab\) are all nonbad. The classical log-free Dirichlet zero-density estimate, in [Klurman, Mangerel and Teräväinen, Lemma 7.3](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/plms.12546), with the exponent weakened from \(12/5+\varepsilon\) to 3, gives
\[
\#\{f_0\le4Q^2:\ f_0\text{ bad}\}
\ \ll\ \big((4Q^2)^2(2T+1)\big)^{3\kappa}
\ \ll\ P^{.4\eta},
\]
since \(3\kappa(4+100)=.312<.4\). Bad single-prime factors eliminate at most \(O(P^{.4\eta}Q)=O(P^{1.4\eta})\) pairs, even counting \(b\) as all integers. Bad products themselves eliminate only \(O(P^{.4\eta})\) further pairs. No possible exceptional real character is treated as good by default.

For a primitive nonprincipal \(\psi\) inducing a nonprincipal character modulo a divisor of a good \(q\), its conductor \(f_0\) is one of \(a,b,ab\). We have uniformly
\[
\sum_{n\le X}\lambda(n)\psi(n)\ll X P^{-50\eta}
\quad(P^{.2}\le X\le2P).
\tag{2}
\]
Here is the fixed-strip check, including the changed conductor bound \(4Q^2\). Use disks of radius \(\kappa/2\) centered at \(1+\kappa/8+it\), \(|t|\le T\), contained in the good zero-free rectangle. Since \(\psi\) is nonprincipal, its partial character sums are \(O(f_0)\) by full periods; partial summation gives a polynomial growth bound \(\log|L(s,\psi)|\ll_\kappa\log(f_0(T+3))\) on these disks. At the center the Euler product bounds the chosen \(\log L\) absolutely by a constant depending on \(\kappa\). Borel--Carathéodory followed by Cauchy on an inner disk gives \(L'/L=O_\kappa(\log(f_0(T+3)))\) on the central half disk. Pick a fixed \(h<\kappa/16\) with \(C_\kappa h<1/5\) for the integrated derivative constant. Integrating from the Euler-product reciprocal point \(1+h+it\) gives \(1/L(s,\psi)\ll_h P^{25\eta}\) for \(1-h\le\Re s\) up to the Perron start line, using \(\log(f_0(T+3))\le(102\eta+o(1))L\). To the right of the inner disk the Euler product suffices.

Truncated Perron for \(\lambda(n)\psi(n)\) uses the exact series \(L(2s,\psi^2)/L(s,\psi)\); the numerator is absolutely bounded throughout because \(2\Re s>3/2\). Use the half-integer endpoint convention and height \(T\). The usual bounded-coefficient truncation error is \(O(XL^2/T)\), the horizontal cost is \(O(XP^{25\eta}/T)\), and the shifted vertical cost is \(O(XX^{-h}P^{25\eta}\log T)\). Choose \(\eta<.2h/100\), as well as \(2\eta<\sigma\) and \(\eta<1/20\). These errors yield (2). The untwisted \(\lambda\) sums at polynomial endpoints use the ordinary arbitrary-log bound, not a constant zero-free strip for \(\zeta\).

## 3. True rough masks by a single global \(L^2\) truncation

For \(w=y,z\), the exact identity
\[
\lambda(n)R_w(n)=\sum_{\substack{v\mid n\\v\ {\rm squarefree},\ P^+(v)\le w}}\lambda(n/v)
\]
follows from the Euler factors. Let \(b_w(n)\) be the same sum truncated at \(v\le P^{1/10}\). If \(w=e^{L^\nu}\), the number \(E_w(n)\) of omitted smooth divisors majorizes the absolute error, \(E_w\le\tau(n)\), and Rankin at exponent \(1/\log w\) gives
\[
\sum_{n\le X} E_w(n)\ll X e^{-cL^{1-\nu}},\qquad
\sum_{n\le X} E_w(n)^2\ll X e^{-c'L^{1-\nu}}
\]
on the polynomial endpoints in use. The first follows from \(\lfloor X/v\rfloor\le X/v\) and the squarefree reciprocal Euler product; the second uses Cauchy with \(E_w^{1/2}\tau^{3/2}\) and the fixed \(\tau^3\) moment. These are deliberately not claimed as power savings pointwise in a twist.

Replace \(g\)'s \(\lambda R_y\) by \(b_y\) to get \(g_b\). For \(f\), write its exact short-slot sum by \(n=p k\), using \(p>z\) and \(\lambda(n)=-\lambda(k)\). Replace the true \(\lambda(k)R_z(k)\) only by \(b_z(k)\), to get \(f_b\). Since \(s(n)\le 1/\sigma\), the square of the source error is bounded by a constant times \(L^2\sum_{p\in\mathcal P,p\mid n}E_z(n/p)^2\). Sum by true endpoints \(P/p\) and \(\sum_{p\in\mathcal P}1/p=O_\sigma(1)\). Hence
\[
\|f-f_b\|_2\ll\sqrt P\,e^{-cL^{.76}},\qquad
\|g-g_b\|_2\ll\sqrt P\,e^{-cL^{1-\delta}}.
\tag{3}
\]
Since the exact and substitute norms are \(O(\sqrt P L)\), Parseval and Cauchy transfer the absolute-integral estimate from \(f_b,g_b\) to the true \(f,g\) on **any frequency set** at arbitrary-log error. This transfer happens once globally. It is not repeated over denominators, and a stretched-log-exponential tail never has to absorb a polynomial Gauss factor.

## 4. All four gcd strata at a good semiprime denominator

Fix \((c',q)=1\) and consider the rational sum of \(b_w(n)\) on an actual interval of scale \(X\gg_J P^{1/2}\), with slow archimedean phase \(e(\beta' n)\), \(|\beta'|X\ll L^{J_0}\), and optional smooth log multiplier of size \(O(L)\) and controlled relative variation. Split into the disjoint strata \(e=(n,q)\), \(e\mid q\), and write \(n=e j\), \(r=q/e\). Then \((j,r)=1\); there is **no** additional requirement \((j,e)=1\), since \(q\) is squarefree. All prime factors of \(e\) exceed \(w\), so exactly \(b_w(ej)=\lambda(e)b_w(j)\), even if \(e,j\) have a common prime. The rational phase becomes \(e(c' j/r)\), and the slow phase remains bounded-variation on the actual \(j\)-scale \(X/e\).

Expand the rational phase on the unit group modulo \(r\). Its principal coefficient is \(\mu(r)/\varphi(r)\), by the squarefree Ramanujan sum since \((c',r)=1\). This is \(O(1/r)\), also at \(r=1\) by convention. To handle the principal character **on units**, expand \(1_{(j,r)=1}\) over \(d\mid r\), substitute \(j=d u\), and use \(b_w(du)=\lambda(d)b_w(u)\). Then open \(v\le P^{1/10}\) in \(b_w\). All actual untreated \(\lambda\)-endpoints have scale at least
\[
X/(e d v)\gg_J P^{.5-2\eta-.1},
\]
since \(e d\mid q\). The slow/log variation is unchanged under these dilations at the actual endpoints. Ordinary untwisted \(\lambda\) cancellation, \(\sum_v1/v\ll\log w\), and the at most four \(d\)'s give \(O_A((X/e)L^{-A})\) for the principal unit sum. Thus after its rational coefficient this particular stratum contributes \(O_A((X/q)L^{-A})\). This includes \(e=q,r=1\) and gives the needed \(1/q\) on all nonunit portions, rather than discarding them synthetically.

For any nonprincipal character modulo \(r\), its primitive inducing character \(\psi\bmod f_0\) has \(f_0>1\) dividing \(r\), so (2) applies by goodness of all \(a,b,ab\). The imprimitive character is exactly \(\psi(j)1_{(j,r/f_0)=1}\) because \(r\) is squarefree. Open this extra unit condition with \(d\mid r/f_0\) (at most the two actual primes), use \(j=d u\), \(\psi(d)\) a unit value, and open \(b_w(u)\) through its \(v\)-sum. Again the true \(\lambda\psi\)-endpoints are \(\gg_J P^{.5-2\eta-.1}>P^{.2}\) and the slow phase costs fixed log powers only. Summing the reciprocal \(d,v\) coefficients with (2) gives \(O((X/e)P^{-45\eta})\), say. The absolute sum of *all* rational multiplicative Fourier coefficients on units is \(\le\sqrt{\varphi(r)}\le \sqrt q\ll P^\eta\) by Parseval, also for imprimitive modes. Thus their total nonprincipal contribution is negligible compared with \((X/q)L^{-A}\). There are only four \(e\)-strata. The common bound is consequently \(O_A((X/q)L^{-A})\) for every reduced numerator and all stipulated \(\beta'\).

Apply this to \(g_b\) with \(X=P,c'=c,\beta'=\beta\). Apply it for each true source prime \(p\in\mathcal P\) to the \(k\)-sum in \(f_b\), with \(X=P/p\ge P^{1/2}\), numerator \(c'=cp\bmod q\), and \(\beta'=\beta p\). Because \(p>P^\sigma>q\) for sufficiently large \(P\), this numerator is reduced. In particular \(|\beta'|X=|\beta|P\le L^{J_0}\). The extra weight \(\log(pk)\) is the allowed smooth log multiplier. Sum over actual \(p\) by \(\sum_p1/p=O_\sigma(1)\). Both \(S_{f_b}\) and \(S_{g_b}\) are therefore \(O_A((P/q)L^{-A})\) on the entire good composite band. Integrating counts at most \(q\) arcs of width \(2L^{J_0}/P\) per product, so their total is \(O_A(PL^{-A}\sum_{q\asymp Q^2}1/q)=O_A(PL^{-A})\). Use (3) to get (1). There is no appeal to prime distribution inside an arbitrary \(\mathcal P\).

## 5. Exact translated selector and scope

For \(f_C=C_{>1}f\), the same actual one-variable integer Selberg estimate as in the prime-denominator note gives
\[
\#\{n\in I:R_z(n)=1,\ C_{>1}(n)=0\}
\ll P L^{-.24-M/200}+P^{.11}.
\]
It uses the true \(jP\) forbidden roots at the translated packets, their distinctness from the baseline zero root, and the genuine greedy cover union; it does not use a factorization of the selector in the composite rational sum. Consequently \(\|f_C-f\|_2\le O(L)\) times the square-root of this count, and \(\|g\|_2^2\ll P L^{-\delta}\). Parseval gives on **any** region, including \(\mathfrak B_2\),
\[
\int |S_{f_C-f}S_g|
\ll P L^{.88-\delta/2-M/400}+P^{.57}
=o(PV_y(P)/L)\quad(M\ge800).
\]
If using only the previously established total-mark deletion \(M\ge400\), (1) is the genuine estimate for the resulting equivalent unmarked target, not a statement about a marked frequency piece at that smaller \(M\).

The proof retains all reduced numerators and the complete ordinary-width neighborhood at each good semiprime denominator. It leaves bad factor/product conductors, unbalanced or more general composite denominators, generic distant minor arcs, and the fixed-target dense coprime off-diagonal slope statistic unestimated.
