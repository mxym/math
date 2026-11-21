# An adaptive positive-envelope obstruction on the actual whole-low ledger

This concerns the original marker \(F\), its high-preserving low lifts, and the actual sequences \(a,b,w\) of [WholeLowCubicHybrid](WholeLowCubicHybrid.md). It rules out a strategy that replaces the unresolved same-target sum by its **physical positive part**, without an estimate pairing opposite scores. It neither rules out a signed upper nor proves Goldbach. Unlike a fixed angular obstruction, the lift can be chosen separately for every target, short divisor, and short physical interval.

## 1. Same complete short-low divisor list

Write \(N=2x\), \(I=(x/2,x]\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), \(D=x^{1/2-\delta}\) with fixed \(0<\delta\le .001\), and \(\alpha=.155\). The weights are
\[
 a(n)=\log(N-n)1_{N-n\ {\rm prime}},\quad
 b(n)=V_0^{-1}1_{P^-(N-n)\ge Z},\quad
 w=a-b,\qquad Z=\exp(L^{1/4}),\quad V_0=\prod_{\ell<Z}(1-1/\ell).
\]
The original marker is \(F(n)=\sum_{d\mid n,d\le D,P^-(d)\ge x^\alpha}\mu(d)\), with \(P^-(1)=+\infty\). Let the lift on a short low divisor \(d\) have coefficient \(\lambda_{N,j}(d)\), allowed to depend arbitrarily on the actual target and divisor, but constant on each physical interval \(I_j\) of a partition of \(I\). Fix any \(C>0\) and allow \(|I_j|\ge x L^{-C}\), even allowing a different such partition for each pair \(N,s=d\). Thus the score on any row with exactly one low divisor \(s\) is \(F(n)+\lambda_{N,j}(s)\). No size bound on \(\lambda\) is needed for the positive-part inequality.

For each actual prime \(s\) with \(\sigma=\log s/L\in[.10,.14]\) define the genuine cohorts
\[
 E_2(s)=\{n=s u\in I:u\ {\rm prime}\},\qquad
 E_3(s)=\{n=s p q\in I:\ p<q\ {\rm primes},\
       x^{.5-\sigma+2\delta}<p,q<x^{.5-2\delta}\}.
\]
These are squarefree for large \(x\), with \(s\) the unique prime below \(x^\alpha\). On \(E_2\), \(u\asymp x/s>\sqrt{x}\), hence \(F=1\). On \(E_3\), both \(p,q\) are eligible; neither \(pq\) nor either of \(sp,sq\) is at most \(D\); hence \(F=1-1-1=-1\). The entire list of short divisors containing a prime below \(x^\alpha\) is literally \(\{s\}\) in both cases. These are respectively in \(\mathcal L_\tau,\mathcal M_\tau\) of WholeLowCubicHybrid for \(\tau<.10\), and the two physical lift scores in the same cell are **exactly** \(1+\lambda\) and \(-1+\lambda\).

## 2. Uniform actual comparison on a same-\(s\) cell

Fix \(N,s,j\) with \(s\nmid N\), and write \(Y=x/s\). Let \(U_i\) be the number of distinct quotients \(n/s\) in \(E_i(s)\cap I_j\). Uniformly in these choices,
\[
 U_2=(1+o(1))\frac{|I_j|}{s(1-\sigma)L},\qquad
 \frac{U_3}{U_2}
   =\log\frac{.5-2\delta}{.5-\sigma+2\delta}+o(1).              \tag{1}
\]
Indeed the PNT on real prefixes with arbitrary-log reserve at polynomial sizes gives the first formula and can be applied to each free \(q\)-interval for fixed \(p\). The limiting integral relative to \(U_2\) is
\[
 \frac12\int_{.5-\sigma+2\delta}^{.5-2\delta}
                  \frac{1-\sigma}{t(1-\sigma-t)}\,dt
\]
for the unordered pair. Replacing \(\log(n/s)/L\) by \(1-\sigma\) changes only a strip of width \(O(1/L)\) in \(t\) at the gates, with uniformly bounded angular density there. At the boundary where a gate truncates an endpoint, use a difference of prime prefix PNTs, with errors negligible even relative to \(|I_j|/s\ge Y L^{-C}\) after summing the harmonic \(p\)-weight. The diagonal \(p=q\) costs \(O(\sqrt Y)\).

Let \(B_i=\sum_{E_i(s)\cap I_j} b(n)\) and \(A_i=\sum_{E_i(s)\cap I_j} a(n)\). We claim the following genuine fixed-cell estimates on the two true sources:
\[
         B_i=(1+o(1))\mathfrak S(N)U_i,\qquad
         A_i\le 4.8\,\mathfrak S(N) U_i  \quad (i=2,3).           \tag{2}
\]
These are not prime-on-prime asymptotics.

For \(E_2\) use ordinary maximal BV on the true prime quotient. For \(E_3\) keep both primes as independent slots and use the full-scale convolution BV ([Maynard, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), as in [FullScaleConvolutionBV](FullScaleConvolutionBV.md)). On each ordinary dyad for the two prime slots both lengths are polynomial in \(Y\), their product is \(\asymp Y\) where the central product interval is nonempty, and the true prime coefficient is Siegel–Walfisz uniformly including the sharp band endpoints. This gives arbitrary-log saving to \(Y^{.49}\), with maximum reduced residue, on the same two-factor source. Compute the convolution as one half of the ordered convolution and subtract equal prime factors. A log-relative grid gives product-prefix uniformity with a log-power cost and boundary strips of size \(Y/L^B\) for an arbitrarily large fixed \(B\). Shiu's divisor-power bound in short reduced APs bounds each strip by \(O(Y L^{-B+O(1)}/\phi(d))\), since \(d\le Y^{.49}\) lies polynomially below that length. The independent factor cuts are part of their own coefficients and need no such mesh. The squares can even be removed by the \(O(Y^{.49}\sqrt Y)\) across all moduli. The moving residue is \(N\overline s\bmod d\) on the true **quotient** source, for the independent reflection divisor \(d\). No distribution theorem modulo the long product \(sp\) is used.

For \(b\) expand the roughness of \(m=N-su\) by upper and lower Bonferroni truncations at \(K=\lfloor L^{1/4}\rfloor\) and adjacent parity. The supported \(d\le Z^{K+1}=x^{o(1)}\). Every source prime exceeds \(Z\), so the coprime principal is \(U_i/\phi(d)\). Since \(s>Z\), a sieve prime \(\ell<Z\) has density \(g(\ell)=1/(\ell-1)\) when \(\ell\nmid N\), and \(g(\ell)=0\) otherwise: in the latter case it would force \(u\equiv0\pmod\ell\), impossible. The aggregate BV error has arbitrary log reserve, absorbing \(V_0^{-1}=O(L^{1/4})\), and the main-term Bonferroni tail is at most \((O(\log L))^K/K!\) times a log power. The exact finite local ratio
\[
 \frac{\prod_{\ell<Z}(1-g(\ell))}{V_0}
 =2\prod_{3\le\ell<Z}\left(1-\frac1{(\ell-1)^2}\right)
       \prod_{\substack{\ell\mid N\\3\le\ell<Z}}\frac{\ell-1}{\ell-2}
 =(1+o(1))\mathfrak S(N)
\]
is uniform in \(N\), with the missing prime-factor tail \(O(L/Z)\).

For \(a\) use the upper dimension-one sieve on \(m\) at \(z_s=Y^{.245}\) and level \(z_s^2\). True \(m\) primes are included. The exact density is \(1/(\ell-1)\) for \(\ell\nmid Ns\), zero otherwise, because \(\ell\mid s,\ell\nmid N\) makes \(m\) a constant unit and no source prime is below \(z_s\). The full local constant is \(\mathfrak S(N)(1+O(1/s)+o(1))\) uniformly. All zero densities (including 2) only improve the dimension-one upper hypothesis. The upper linear sieve at \(s_{\rm sieve}=2\) has \(F(2)=e^\gamma\), so after \(\log m\le L+O(1)\) the factor is at most
\[
                \frac{1+o(1)}{.245(1-\sigma)}<4.8 .
\]
Arbitrary-log saving in BV at \(Y^{.49}\) pays the sieve error relative to \(U_i\asymp |I_j|/(s L)\). The factor intervals keep every \(p,q>x^{.36}\), whereas \(z_s<x^{.221}\), so no prime factor of the source is accidentally excluded by the reduced principal. If \(s\mid N\), there are no genuine reflected primes in either cell because \(m\ge x>s\).

On true prime \(m\), \(b(n)=V_0^{-1}=O(L^{1/4})\), so \(w>0\) for large \(x\); elsewhere \(w=-b\le0\). Put
\[
 X_2=\sum_{E_2(s)\cap I_j}[w]_+,\qquad
 Y_3=\sum_{E_3(s)\cap I_j}[-w]_+ .
\]
Thus \(Y_3\) is the rough-reference mass on **composite** reflected \(m\), not the entire \(B_3\). The genuine prime \(m\) part of \(B_3\) costs only \(O(L^{-3/4}A_3)\) by (2). At the worst endpoint the log ratio in (1) is at least \(\log(.498/.402)\ge2(.498-.402)/(.498+.402)>.21\). Eventually and uniformly,
\[
                 X_2\le4.8\,\mathfrak S(N)U_2,\qquad
                 Y_3\ge .20\,\mathfrak S(N)U_2 .              \tag{3}
\]

## 3. Arbitrary adaptation still incurs the positive-part cost

Write \(K=F+\lambda\) on the two chosen cohorts. In each actual \((N,s,j)\) cell and for **any** real \(\lambda\),
\[
 \sum_{(E_2(s)\cup E_3(s))\cap I_j} [w(n)K(n)]_+
   \ge X_2[1+\lambda]_++Y_3[1-\lambda]_+
   \ge 2\min(X_2,Y_3)\ge X_2/12.                                \tag{4}
\]
This holds also for \(s\mid N\) since \(X_2=0\). One may choose the lift after knowing both same-target occupations. The uniform per-cell upper on \(X_2\) and lower on \(Y_3\) are necessary: minimizing the dyadic average over \(\lambda\) would not justify adaptation.

For every large dyad there is an actual even target at which this positive-part envelope exceeds \(.031M_N\), **uniformly** over all these assignments of the lift. In fact
\[
 \frac{\sum_{2X<N\le4X,\ 2\mid N}\ \sum_{s,j} X_2(N,s,j)}
      {\sum_{2X<N\le4X,\ 2\mid N} M_N}
 \ \longrightarrow\int_{.10}^{.14}\frac{dt}{t(1-t)}
                  =\log(63/43)>.372 .                            \tag{5}
\]
For (5), sum over independent actual primes \(s,u,m\) with \(n=su\) and \(N=n+m\). The even condition is automatic, since all three primes are odd. The central inequalities say \(n\le m<3n\), and the target dyad says \(2X<n+m\le4X\). The weight of \(m\) is \(\log m(1+o(1))\) after subtracting \(V_0^{-1}\). Replacing the moving \(\log_x s\) band by the \(\log_X s\) band costs prime harmonic \(o(1)\), as \(\log x=\log X+O(1)\). Boundaries in the two physical axes have zero area and can be squeezed by fixed rectangles. On those rectangles PNT for independent prime prefixes gives density \(\int_{.10}^{.14}dt/[t(1-t)]\) divided by \(\log X\) in the \(n\)-axis and density \(1\) in the \(m\)-axis after its log weight. The map to \((N,n)\) has determinant 1 and \(n\)-length \(x/2\) for each \(N\). The binary singular series has mean 2 over even targets, exactly compensating the spacing 2. For the positive divisor expansion of \(\prod_{\ell\mid N,\ell>2}(1+1/(\ell-2))\), the coefficients \(h(d)\) have \(\sum_{d\le 4X}h(d)=O(\log X)\) by the Euler majorant and Mertens, and \(\sum h(d)/d\) converges to the inverse twin-prime product. Counting even multiples of odd \(d\) and then partial summation gives the stated mean also with weight \(x/(2L)\). Hence (5) uses the **sum of \(M_N\)**, not an unweighted mean of per-target ratios. The elementary \(\log(63/43)\ge 2(63-43)/(63+43)>.372\) makes the .031 bound strict in (4) and (5).

The same obstruction applies to uniformly bounded equicontinuous lifts in \(n/x\), by replacing them with their sampled values on a fixed fine mesh and using (2) for the absolute error \(O(M_N)\) times their modulus of continuity. The hybrid cubic lift has this property, with its literal \(f_\delta(\log s/\log n)\). This does not allow arbitrary dependence on the arithmetic value of \(n\) beyond the stated divisibility data, which could distinguish the two cohorts. It also does not apply to an estimate that uses signed cancellation across physical rows. The remaining arithmetic is a **reflected prime** comparison on the same quotient sources \(u\) prime and \(u=pq\) balanced. Actual product BV and common sieve give both \(b\)-references and separate upper bounds, but no signed comparison of \(A_2,A_3\). No reserve is extracted for the actual \(.00659M_N\) whole-low signed budget.

[check_adaptive_whole_low_collision.py](check_adaptive_whole_low_collision.py) certifies the rational margins and exercises the divisor and positive-part identities exactly.
