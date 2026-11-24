# The fixed-target slope dispersion has negligible shared gcd and an exact coprime normalization

Research note, 2026-11-24. Companion to [the mixed marker](SmallRadicalG23CoreBilateral.md) and [the good-prime-denominator note](SmallRadicalGoodPrimeDenominatorArcs.md). This pays every actual noncoprime off-diagonal pair and computes the unsigned scale of the dense coprime remainder using genuine prime distribution. The normalized signed second moment on that remainder is not proved.

## 1. Exact global dispersion after the true mark deletion

Let \(P\) be large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), fixed \(0<a<b<1\), \(I=[aP,bP]=PJ\), \(y=e^{L^\delta}\), \(0<\delta<.1\), and \(z=e^{L^{.24}}\). Write \(R_t(u)=1_{P^-(u)>t}\), \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\asymp L^{-.24}\), \(V_y=V_y(P)=\prod_{\ell\le y,\,\ell\nmid P}(1-1/(\ell-1))\asymp S(P)L^{-\delta}\). Fix \(0<\sigma<1/4\) and \(D=P^{1/2}e^{-L^{3/5}}\). In the normalization below take the full true prime range \(\mathcal P=\{p\text{ prime}:P^\sigma<p\le D\}\); the upper and gcd estimates work for any subset.

The actual translated first-cover marked mixed \(G_{23}\) statistic differs from its unmarked version by \(o(PV_y/L)\) for fixed \(M\ge400\), by the genuine integer co-sieve previously proved. This is a deletion for the additive **total**, not for its frequency-restricted integral. If desired, the earlier \(M\ge800\) Parseval version works on arbitrary frequency sets as well. The source is \(n=pk\) and \(\lambda(n)=-\lambda(k)\) for each true \(p\mid n\), with \(p>z\). Define
\[
\begin{aligned}
W(p,k)&=1_{\{pk\in I\}}\,\log(pk)/L,\\
A(k)&=\sum_{p\in\mathcal P} W(p,k)R_y(P-pk)\lambda(P-pk),\\
B_0(k)&=\sum_{p\in\mathcal P} W(p,k)R_y(P-pk).
\end{aligned}
\]
Take undefined reflected expressions to be zero when \(pk\notin I\). Then the unmarked mixed total is exactly \(-L\sum_k R_z(k)\lambda(k)A(k)\). Its \(k\)-range is contained in \([aP/D,bP/P^\sigma]\). Weighted Cauchy, without summing absolute values box by box, gives
\[
|\mathcal M|^2
\le L^2\left(\sum_k \frac{R_z(k)}k\right)\mathcal Q_k,\quad
\mathcal Q_k=\sum_k k R_z(k)|A(k)|^2
=\mathrm{Diag}_k+\mathcal D_k.
\tag{1}
\]
Here \(\mathcal D_k\) is the actual signed off-diagonal
\[
\sum_{\substack{p,p'\in\mathcal P\\p\ne p'}}\sum_k
 k R_z(k)W(p,k)W(p',k)
 R_y(P-pk)R_y(P-p'k)\lambda(P-pk)\lambda(P-p'k).
\tag{2}
\]
In particular both source product windows and both real reflected rough filters are present. The full diagonal satisfies
\[
0\le \mathrm{Diag}_k\ll \sum_{p\in\mathcal P}(P/p)^2
\ll P^{2-\sigma},
\tag{3}
\]
since all coefficients except \(k\) are bounded and the true \(k\)-interval for each \(p\) is \(O(P/p)\). This is power-negligible even after Cauchy.

## 2. Complete absolute payment of the noncoprime pairs

Put \(m_p=P-pk\), \(m_{p'}=P-p'k\) on a retained term of (2). Because \(R_z(k)=1\) and \(\operatorname{rad}(P)<z\), \((k,P)=1\). If \(\ell\) divides both reflected integers, \(\ell>y\), \(\ell\nmid Pk\), and \(\ell\nmid p,p'\): otherwise one of the exact relations would force \(\ell\mid P\). Subtracting gives \(\ell\mid(p-p')\). In fact the full gcd divides \(p-p'\), since it is coprime to \(k\), but a single common prime suffices. The actual \(k\) condition is the one reduced class
\[
k\equiv Pp^{-1}\pmod\ell .
\tag{4}
\]

Whenever \(W(p,k)W(p',k)\ne0\), \(p\asymp_J p'\). Partition the first \(p\) into \(O(L)\) fixed relative boxes \(p\asymp X\) and permit \(p'\) in the resulting bounded larger relative range also of scale \(X\). Then \(k\asymp_J Y=P/X\), \(Y\gg_J X\) because \(p,p'\le D\), and \(\ell\ll_J X\) for \(p\ne p'\). Even ignoring that \(p,p'\) are prime, the number of pairs with \(p\equiv p'\pmod\ell\) is \(O_J(X^2/\ell)\): for each of \(O(X)\) integers \(p\) there are \(O(X/\ell+1)=O_J(X/\ell)\) choices. For each pair (4) gives \(O_J(Y/\ell+1)=O_J(Y/\ell)\) actual \(k\)'s; this is exactly why the large shared-prime floors do not hurt. Sum over all possible \(\ell>y\) and use \(k\ll Y\). In one box the entire **absolute** bill is at most
\[
O_J(X^2Y^2\sum_{\ell>y}\ell^{-2})=O_J(P^2/y).
\]
For all boxes it is \(O_J(P^2 L/y)\), super-logarithmically small. Numerical double-counting of rows with several common primes only enlarges this upper bound. The same proof without the weight \(k\) gives the original single-box \(O(X^2Y/y)\) bound. There is no surviving shared-gcd sign effect of the requisite size. Complete multiplicativity would cancel a common divisor's sign in \(\lambda(m_p)\lambda(m_{p'})\), but abundance need not be inferred from that identity.

## 3. True unsigned normalization, including its leading constant

For each fixed genuine rough \(k\) in the source range, every prime \(p\) in its allowed interval exceeds \(y\), and \(k\) is a unit at each \(\ell\le y\). If \(\ell\mid P\) then \(\ell\nmid P-pk\) automatically. For every other \(\ell\le y\), the only forbidden residue for \(p\) is the **reduced** class \(Pk^{-1}\bmod\ell\). Uniformly in all such \(k\), true prime Bombieri--Vinogradov therefore gives
\[
B_0(k)
=V_y\int_{[aP/k,bP/k]\cap[P^\sigma,D]}
    \frac{\log(tk)/L}{\log t}\,dt
 +O_A((P/k)L^{-A}).
\tag{5}
\]
To see the uniform error, open the forbidden classes by the upper/lower Bonferroni polynomials through \(C_A\log L\) factors. Every retained squarefree modulus is \(P^{o(1)}\) and gives one reduced progression. Ordinary maximal log-prime BV at the **actual endpoint** \(O_J(P/k)\ge P^{\sigma-o(1)}\) is uniform in its moving endpoint and residue. Factorial reciprocal tails with \(\sum_{\ell\le y}1/(\ell-1)=O(\log L)\) give arbitrary log saving; the smooth multiplier \((\log(tk)/L)/\log t\) is bounded with controlled variation on the physical interval. Thus (5) counts the true prime \(p\), not replacement integers. The argument works even when the endpoint intersection is empty or short.

Now for \(bP/D\le k\le aP/P^\sigma\), put \(u=\log k/L\). The whole \(I/k\) interval is present, \(\log(tk)/L=1+O_J(1/L)\), and \(\log t=L(1-u)+O_J(1)\). Since \(1-u\ge\sigma+o(1)\), its integral in (5) is
\[
\frac{P |J|}{k L(1-u)}(1+O_{\sigma,J}(1/L)),\qquad |J|=b-a .
\tag{6}
\]
The two omitted \(k\)-end strips have bounded logarithmic length, and everywhere the integral in (5) is \(O_{\sigma,J}(P/(kL))\). The pure-integer rough count has density \(\kappa_z\) with arbitrary-log prefix error uniformly over these polynomial scales (ordinary integer Bonferroni, where the retained products have logarithms \(O(L^{.24}\log L)\)). Partial summation in \(k\), or fixed relative endpoint subdivision, gives
\[
\begin{aligned}
\sum_k R_z(k)/k&\sim \kappa_z L(1/2-\sigma),\\
\sum_{bP/D\le k\le aP/P^\sigma}
 \frac{R_z(k)}{k(1-\log k/L)^2}
&\sim \kappa_z L\int_{1/2}^{1-\sigma}(1-u)^{-2}\,du
=\kappa_z L(1/\sigma-2).
\end{aligned}
\]
The first prefix uses the full source \(k\)-support range as an upper set, not a prior nonvanishing theorem for its signed weights. The \(k\)-boundary strips contribute \(O(\kappa_z)\) to the unweighted harmonic sum. The lower limit in the second line differs from \(1/2\) by \(L^{-2/5}+O(1/L)=o(1)\), which does not affect its limiting constant.

Therefore the genuine unsigned weighted second moment satisfies
\[
\mathcal U_k:=\sum_k k R_z(k)B_0(k)^2
\sim |J|^2(1/\sigma-2)\frac{P^2\kappa_z V_y^2}{L}.
\tag{7}
\]
The error in (5) is arbitrary-log small also after squaring and summing, using \(V_y\gg L^{-\delta}\) and the harmonic \(k\)-weight. Remove the diagonal and then all genuine noncoprime reflected pairs from this square: (3) and §2 show the same leading asymptotic (7). Thus the actual **coprime** off-diagonal is dense even with both rough conditions and the entire true prime-slope range. In particular rarity of shared prime factors is not a rarity of the off-diagonal being estimated.

## 4. The weaker one-sided target and its meaning

It suffices in (1) to have the one global signed, \(k\)-weighted inequality
\[
\mathcal D_{k,\mathrm{coprime}}\ \le\
 o\!\left(\frac{P^2V_y^2}{\kappa_z L^5}\right).
\tag{8}
\]
No absolute pointwise bound on each box, no control of a negative contribution, and no averaging in \(P\) are needed. The removed gcd and diagonal terms are negligible at this scale by §§1–2. In view of the exact unsigned denominator (7), (8) asks for the positive side of the true normalized signed off-diagonal to be \(o(L^{-88/25})\), since \(1/(\kappa_z^2L^4)\asymp L^{-88/25}\). This is weaker and better scaled than an arbitrary-log bound in every box. It is still unproved.

Equivalently, put \(b(k)=A(k)/B_0(k)\) when \(B_0(k)>0\) and zero otherwise, and weight \(k\) by \(kR_z(k)B_0(k)^2/\mathcal U_k\). A sufficient (and same-size here, up to negligible diagonal) statement is \(\mathbb E[b(k)^2]=o(L^{-88/25})\). This is an averaged **squared parity bias on true primes \(p\)** with the actual affine complement \(P-pk\), fixed \(P\), and all original rough restrictions. The exact distribution (5) controls only the unsigned denominator. Ordinary single-function BV or fixed-coefficient Chowla does not control this variance: \(k\) is polynomial and can exceed the ordinary BV range as a sampling modulus, and the \(p,p'\) slopes and common intercept in (2) all vary with the target's size. Removing the coprimality check therefore clarifies the genuinely dense remaining problem; it does not establish its signed cancellation.
