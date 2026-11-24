# The true shifted-tag off-diagonal: removable bad sets and what remains

This concerns a genuine \(\Gamma\) expansion for the residual in [the translated-tag reduction](SmallRadicalTranslatedTagTypeI.md). It is not a bound on the full shifted \(\Gamma\), nor a two-point Chowla theorem.

## 1. Exact Cauchy setup and moments

Keep a fixed even \(P\) with \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), a fixed offset \(j\ge2\), and \(c=j-1\). Put \(y=\exp(L^\delta)\), \(0<\delta<.1\). Work in one tag shell \(u\in[Y,2Y]\) of one admissible family of \(K\) primes from packet bands, so \(Y=P^{o(1)}\), \(Y\ge\exp(L^{.105})/O(1)\), and all primes dividing \(u\) are \(\ge\exp(L^{.105})\). The argument also applies to narrower shells.

Let \(F_u(h)\) be a Vaughan Type II product sum at \(n=jP-u h\in I=PJ\), with pair coefficients of fixed polylogarithmic size. It may already impose the original \(z\)-rough support, the residual high range, and box restrictions. Only \(|F_u(h)|\ll L^{C_0}\tau(n)\) is needed below. The exact shifted selector yields a multiplier
\[
B_u(h)=A_u(h)1_{\{P^-(uh-cP)>y\}}\lambda(uh-cP),\qquad |A_u(h)|\le1,
\]
which may depend on all actual offsets, \(h,u\). After fixed \(j,I,Y\), any occurring \(h\) lies in an interval of length \(O_J(P/Y)\) and is positive; use one common containing interval \(\mathcal H\). Cauchy in \(h\) gives, for \(T=\sum_{h,u}F_u(h)B_u(h)\),
\[
|T|^2\le O_J(P/Y)Q,\qquad
Q=\sum_{h\in\mathcal H}\sum_{u,u'} F_u(h)\overline {F_{u'}(h)} B_u(h)\overline {B_{u'}(h)}.
\tag{1}
\]
For each \(n\), the tag \(u\) must divide \(jP-n\) and determines \(h\) uniquely. Each such shifted integer admits at most \(O_K(L^K)\) tag products: choose one from each of \(K\) colour bands. Thus
\[
\sum_{u,h}|F_u(h)|^2+\sum_{u,h}|F_u(h)|^4
\ll P L^{C_1}
\tag{2}
\]
for fixed \(C_1\), by the ordinary divisor moments \(\sum_{n\le P}\tau(n)^k\ll P L^{2^k-1}\) for \(k=2,4\). The crude bound follows from \(\tau(n)^k\le\tau_{2^k}(n)\). No pointwise \(\tau=P^{o(1)}\) is multiplied against a subpower exponential saving.

## 2. Three individually negligible exact bad sets

Here the absolute sums on the bad terms of (1) are considered, so no cancellation is assumed of \(\lambda\) or the selectors.

* **Tags sharing a prime, including the diagonal.** For fixed \(u\), at most \(\sum_{q\mid u}O(Y/q)\ll_K Y e^{-L^{.105}}\) shell tags \(u'\) share one of its \(K\) primes, by counting all multiples in the shell. This also absorbs a possible floor \(+1\) since \(q\le u\le2Y\). Apply \(2ab\le a^2+b^2\) to \(|F_u(h)F_{u'}(h)|\), sum in the symmetric adjacency relation of common factors, and use (2). The resulting contribution is \(O(PY L^{C_1}e^{-L^{.105}})\).
* **Close, differing tags.** Similarly each \(u\) has at most \(O(Y/L^D+1)\) tags at distance \(\le Y/L^D\). Since \(Y\) grows faster than every fixed power of \(L\), the resulting absolute contribution is \(O(PY L^{C_1-D})\). Choose \(D\) as a sufficiently large fixed power after the desired saving. Neither of these two removals uses arbitrary-residual Type II.
* **Shared rough prime in the two sign arguments.** On the remaining off-diagonal \(u\ne u'\), suppose a prime \(r\) divides both \(m=uh-cP\) and \(m'=u'h-cP\), with both \(y\)-rough. Then \(r>y>\operatorname{rad}(cP)\), so \(r\nmid cP\). In particular \(r\nmid h\) and \(r\nmid u\); subtracting the arguments gives \(r\mid u-u'\), and \(h\equiv cP u^{-1}\pmod r\). For each ordered pair \(u,u'\), the number of offending primes is \(\ll \log(2Y)/\log y\ll L^{C_2}\); for each, the number of exact eligible \(h\)'s is at most \(O((P/Y)/r+1)\). With at most \(O(Y^2)\) ordered pairs, the bad triple count is therefore
\[
\ll P Y L^{C_2}/y+Y^2 L^{C_2}.
\]
The second term is the entire long-modulus floor bill, not a per-pair asymptotic. Also
\[
\sum_{u,u',h}|F_u(h)F_{u'}(h)|^2
=\sum_h\Big(\sum_u|F_u(h)|^2\Big)^2
\ll Y\sum_{u,h}|F_u(h)|^4\ll P Y L^{C_1}.
\]
Apply Cauchy to the sum on the bad triples. Its absolute contribution is
\[
\ll PY L^{O(1)}(y^{-1/2}+(Y/P)^{1/2}),
\]
again smaller than any fixed inverse log since \(y\) is stretched exponential and \(Y=P^{o(1)}\). If residual signs are Möbius, the same bounds still apply. For Liouville these removals are useful observables even though complete multiplicativity also holds with common factors.

Thus arbitrary-log power control of the remaining non-shared, separated sparse-tag part of \(Q\) would suffice for the relevant shell in (1). The remaining affine forms \(u h-cP\) and \(u'h-cP\) have determinant \(cP(u'-u)\neq0\), with **two growing slopes, a growing intercept, actual bilinear channel weights, and exact selectors**. The [ordinary two-point Chowla paper](https://github.com/openai/math/tree/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026) states its ordinary estimate for fixed affine forms without uniformity in these parameters; it does not cover this problem even before the weights. No claim is made about the sign, mean magnitude, or pointwise bound for this remaining \(\Gamma\).

## 3. Why the obvious character separation does not lose merely a few logs

The physical endpoints in [the projected minor comparison](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/target_slope_switch/Proof.md) are \((D c' m_1,s_1)\) and \((D a' r_1,n_1)\) in its notation. The old bilinear weights can be paired as \((\alpha_{m_1}\overline{\beta_{s_1}})(\overline{\alpha_{r_1}}\beta_{n_1})\), one product per endpoint. The new weight \(\lambda(P-m_1n_1)\) depends on variables from **opposite** endpoints, before even including the first-cover selector. Hence no direct diagonal conjugation of that operator accounts for it.

A formal way to restore separation would be to expand \(f(x)=\lambda(P-x)1_{\{x\in I,\ P^-(P-x)>y\}}\) in the multiplicative characters of \((\mathbb Z/P\mathbb Z)^\times\), representing \(x\) between 1 and \(P-1\). This factors each term's character when \(x=m_1 n_1\in I\), but absolute summation of characters is genuinely too expensive. Normalize \(\widehat f(\chi)=\phi(P)^{-1}\sum_x f(x)\overline{\chi(x)}\). The [small-radical projected major proof, §1](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Proof.md) shows uniform arbitrary-log prime-independent Möbius character cancellation at polynomial lengths for all \(P\)-characters. To see that it gives the needed \(\lambda\)-rough version, use \(\lambda(n)=\sum_{d^2\mid n}\mu(n/d^2)\). The tail \(d>P^{1/10}\) costs \(O(P^{9/10})\) by counting floor multiples. For smaller \(d\), the variable \(n/d^2\) ranges in interior intervals at polynomial length. The same rough restriction as in that proof works with the smaller \(y\): at primes \(\ell\le y\), cancel the local \(\mu\chi\) factor by convolving with the \(\chi\)-weighted \(y\)-smooth indicator; split its dilation variable at \(P^{1/10}\) by Rankin. The tail reciprocal mass is \(O((\log y)e^{-c_0 L^{1-\delta}})\), and the retained endpoints still have polynomial length. The modulus remains \(P\) throughout. Hence, since \(\chi(P-x)=\chi(-1)\chi(x)\) on units and \(P/\phi(P)\ll L\), \(\max_\chi|\widehat f(\chi)|\ll_A L^{-A}\) for every fixed \(A\).

On the other hand, Parseval gives
\(\sum_\chi|\widehat f(\chi)|^2=\phi(P)^{-1}\#\{x\in I:P^-(P-x)>y\}\gg L^{-\delta}\).
The integer rough count follows from truncated Bonferroni at depth \(\lfloor L^{.1}\rfloor\), using exact CRT floors at subpower moduli and the usual Mertens product; the rough condition already makes \(x,P-x\) target units. Therefore \(\sum_\chi|\widehat f(\chi)|\ge\sum_\chi|\widehat f(\chi)|^2/\max_\chi|\widehat f(\chi)|\) grows faster than every fixed power of \(L\). This does not rule out a weighted cancellation across the character terms, but it rules out restoring factorization by the naive absolute sum of arbitrary-log estimates one character at a time.
