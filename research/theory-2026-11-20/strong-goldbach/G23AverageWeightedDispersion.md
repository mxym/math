# The genuine G23 slope-dispersion is log-small outside a log-sparse set of targets

Written research note, 2026-11-24. This is an average across targets \(P\), not a fixed-target theorem. It bounds the nonnegative weighted square which controls the G23 mixed statistic, not just the scalar mixed statistic after cancellations between the \(k\)'s. The unmarked theorem needs neither a bound on \(\operatorname{rad}(P)\) nor prime progression distribution.

## 1. Statement

Fix \(J=[a,b]\Subset(0,1)\), \(0<\sigma<1/4\), and \(0<\delta<.1\). For each integer \(P\in[X,2X]\), put \(L_P=\log P\), \(y_P=e^{L_P^\delta}\), \(z_P=e^{L_P^{.24}}\), \(D_P=P^{1/2}e^{-L_P^{3/5}}\) and \(R_v(m)=1_{P^-(m)>v}\) for positive integers. With \(A_P(k)\) defined by the original exact moving endpoints, set
\[
 A_P(k)=
 \sum_{\substack{p\ {\rm prime}\\ P^\sigma<p\le D_P\\ aP\le kp\le bP}}
 \frac{\log(kp)}{L_P}R_{y_P}(P-kp)\lambda(P-kp),\qquad
 \mathcal Q_P=\sum_k kR_{z_P}(k)|A_P(k)|^2 .
\]
Then for any fixed \(A>0\),
\[
 \sum_{X\le P\le2X}\sum_k k|A_P(k)|^2\ll_{A,J,\sigma,\delta}X^3(\log X)^{-A}.
 \tag{1}
\]
This is stronger than the same bound on \(\sum_P\mathcal Q_P\): the outer rough selector has been dropped only in an upper bound on a nonnegative square, not from the original statistic. In particular, for any \(F,E>0\), all but \(O_{F,E}(X/(\log X)^F)\) of these integers (or of these even integers) satisfy \(\mathcal Q_P\ll_{F,E}P^2(\log P)^{-E}\). All constants may depend on the fixed parameters above. The upper bound also permits replacing the true prime-supported coefficient \(1\) by any fixed \(|c_p|\le1\), independent of \(P,k\); no lower bound for such arbitrary coefficients is claimed.

## 2. Rough Liouville on the full frequency circle

Write \(L=\log X\), \(e(t)=e^{2\pi i t}\), \(b_u(m)=1_{1\le m\le 2X}\lambda(m)R_u(m)\), and \(\widehat b_u(\alpha)=\sum_m b_u(m)e(m\alpha)\). Uniformly for \(3\le u\le e^{2L^\delta}\),
\[
 \sup_{\alpha\in\mathbb R/\mathbb Z}|\widehat b_u(\alpha)|\ll_C XL^{-C}
 \tag{2}
\]
for each fixed \(C\). Indeed Davenport's exponential-sum estimate for \(\mu\), in [On some infinite series involving arithmetical functions (II), 1937](https://doi.org/10.1093/qmath/os-8.1.313), gives the same estimate on \(\lambda\) by \(\lambda(m)=\sum_{d^2\mid m}\mu(m/d^2)\): apply Davenport on \(d\le X^{1/4}\) and bound the remaining terms by \(O(X\sum_{d>X^{1/4}}d^{-2})\), also with \(X\) replaced by any large argument. With \(P_u=\prod_{\ell\le u}\ell\), complete multiplicativity and \(\mu(d)\lambda(d)=1\) on the squarefree divisors of \(P_u\) give the exact formula
\[
 \widehat b_u(\alpha)=\sum_{d\mid P_u}\sum_{j\le 2X/d}\lambda(j)e(dj\alpha).
\]
For \(d\le\sqrt X\), use the true endpoint \(2X/d\) in the preceding \(\lambda\) bound and \(\sum_{d\mid P_u}d^{-1}\ll\log u\). For \(d>\sqrt X\), use the trivial count \(2X/d\). With \(\theta=1/\log u\), its reciprocal tail is
\[
 \sum_{\substack{d\mid P_u\\d>\sqrt X}}d^{-1}
 \le e^{-L/(2\log u)}\prod_{\ell\le u}(1+\ell^{-1+\theta})
 \ll e^{-L/(2\log u)}(\log u)^e,
\]
by \(\ell^\theta\le e\) and Mertens. This pays every fixed log power. The other bound we use is just \(\int_0^1|\widehat b_u|^2\le2X\).

## 3. Frozen \(u\): a simultaneous dispersion bound for moving source intervals

Only dyadic blocks \(K\le k<2K\) with \(c_J\sqrt X\le K\le C_J X^{1-\sigma}\) are needed, enlarging fixed constants to include intersecting blocks. Put \(U=X/K\). For each such block, all needed slopes lie in a fixed integer interval \([c_JU,C_JU]\): this follows from \(aP\le kp\le bP\), irrespective of the sharper endpoints \(P^\sigma,D_P\). In particular \(U\gg_J X^\sigma\) and \(U\ll_J\sqrt X\).

Pad that fixed interval to a consecutive array of length a power of two and comparable to \(U\), and give it its binary interval tree \(\mathscr B\). At a node \(B\), use the true coefficient
\[
 S_{B,k}(\alpha)=\sum_{\substack{p\in B\\p\ {\rm prime}}}c_p e(kp\alpha),\qquad
 F_{B,k}(P)=\sum_{\substack{p\in B\\p\ {\rm prime}}}c_p b_u(P-kp).
\]
One may put \(c_p=0\) on any padding outside the fixed interval. Every allowed \(p\)-interval, and every prefix of that interval, is a disjoint union of \(O(L)\) tree nodes. For the actual log weight \(f(p)=\log(kp)/L_P\) on the allowed physical interval, \(\sup |f|\le1\) and its total variation is at most 1. Abel summation thus bounds a weighted sum by twice its maximum absolute prefix. Cauchy on the disjoint node decomposition of each such prefix therefore gives
\[
 |A_{P,u}(k)|^2\ll L\sum_{B\in\mathscr B}|F_{B,k}(P)|^2,
 \tag{3}
\]
where \(A_{P,u}\) is the actual definition with only \(y_P\) replaced by \(u\). This handles the exact \(D_P\) and all physical endpoints without any smoothing, freezing, or endpoint error.

For a single tree level \(\mathscr B_d\), define
\[
 E_d(\alpha)=\sum_{K\le k<2K} k\sum_{B\in\mathscr B_d}|S_{B,k}(\alpha)|^2.
\]
Its naive upper is \(O(K^2U^2)=O(X^2)\), since \(\sum_B N_B^2\le(\sum_B N_B)^2\ll U^2\), with \(N_B=\#\{p\in B:p\ {\rm prime},\ c_p\ne0\}\). More importantly,
\[
 E_d(\alpha)\ll K^2U+KU\sum_{1\le h\le C_JU}\min(K,\|h\alpha\|^{-1}),
 \tag{4}
\]
with \(1/0=+\infty\). The diagonal has \(\sum_B N_B\ll U\) and each diagonal \(k\)-sum is \(O(K^2)\). In the off diagonal, for each given positive \(h\) the pair multiplicity summed over this one level is \(O(U)\): each \(p\) belongs to at most one node and \(p+h\) is uniquely determined. The separate factor \(K\) comes from Abel's weighted geometric progression bound
\(\left|\sum_{K\le k<2K} k\,e(kh\alpha)\right|\ll K\min(K,\|h\alpha\|^{-1})\).
The same holds for negative \(h\). This computes the \(KU\) prefactor; there is not a second multiplicity \(U\).

Choose \(B_0>0\) large and \(Q=\lfloor X/L^{B_0}\rfloor\). For each \(\alpha\), Dirichlet gives a reduced \(r/q\) with \(q\le Q\) and \(|\alpha-r/q|\le1/(qQ)\) mod 1. If \(q\le L^{B_0}\), this point lies on the union of intervals \(|\alpha-r/q|\le1/(qQ)\) about all such reduced fractions. Their total measure is \(O(L^{2B_0}/X)\). On the complement we have \(L^{B_0}<q\le Q\) and \(|\alpha-r/q|\le1/q^2\). For each successive block of at most \(q/2\) positive \(h\)'s, the mod-1 points \(h\alpha\) have pairwise spacing \(\ge1/(2q)\): their nonzero differences \(d\) have \(\|dr/q\|\ge1/q\) and error \(\le d/q^2\le1/(2q)\). The nearest point costs at most \(K\); the rest sum to \(O(q\log(2q))\). Thus the sum in (4) is \(O((U/q+1)(K+q\log(2q)))\). Relative to \(X^2\), the terms in (4) are bounded by constants times
\[
 \frac1U+\frac1q+\frac{U\log(2q)}{X}+\frac{q\log(2q)}{X}.
\]
All are \(O_{J,\sigma}(L^{1-B_0})\) in this range, with the power-small terms absorbed for fixed \(B_0\).

Now Parseval in the target variable \(P\) gives the exact formula
\[
 \sum_{P\in\mathbb Z}\sum_{K\le k<2K}k\sum_{B\in\mathscr B_d}|F_{B,k}(P)|^2
 =\int_0^1|\widehat b_u(\alpha)|^2E_d(\alpha)\,d\alpha.
 \tag{5}
\]
On the small-denominator union, use the naive \(O(X^2)\) for \(E_d\), (2) and the arc measure to bound the integral by \(O_C(X^3L^{2B_0-2C})\). Outside, use the saving in \(E_d\) and the unweighted \(\widehat b_u\) Parseval bound to get \(O(X^3L^{1-B_0})\). Choose \(B_0\) and then \(C\) for any desired log saving. The tree overhead is \(O(L^2)\): one \(L\) from (3), then \(O(L)\) levels, with (4) valid for each level's total, not once per node. Summing \(O(L)\) distinct dyadic \(K\)-blocks adds just one more log. The resulting frozen-\(u\) bound is \(O_N(X^3L^{-N})\) for every fixed \(N\), uniformly in \(u\) in (2).

## 4. The exact moving rough cutoff

For fixed auxiliary \(D_0>0\), partition \([X,2X]\) into \(O(L^{D_0})\) intervals \(\mathcal S_i\) of length \(\ll X/L^{D_0}\). Freeze \(y_P\) at its within-slab lower endpoint \(u_i\); let \(v_i\) be the upper endpoint. Since the derivative of \((\log t)^\delta\) is \(\delta(\log t)^{\delta-1}/t\), one has
\(\log(v_i/u_i)\ll L^{\delta-1-D_0}\). Even summing over all integers instead of primes shows
\[
 \rho_i:=\sum_{u_i<\ell\le v_i,\ \ell\ {\rm prime}}\ell^{-1}
 \ll L^{\delta-1-D_0}+e^{-cL^\delta},
 \qquad
 \#\{\ell:u_i<\ell\le v_i\}\le e^{2L^\delta}.
\]
For each actual \(p,k\), as \(P\) runs over this slab, \(m=P-kp\) runs over a translated interval of the same length. The event \(R_{y_P}(m)\ne R_{u_i}(m)\) on positive \(m\)'s requires some such \(\ell\mid m\), so is counted at most
\[
 O((X/L^{D_0})\rho_i+e^{2L^\delta})
\]
times by the true modulus floors. This bound uses the slab's actual length, not a full dyadic interval for each \(i\). Since \(|R_{y_P}-R_{u_i}|^2\) is the indicator of the change and \(|Wc_p\lambda|\le1\), Cauchy in at most \(O(U)\) possible \(p\)'s gives
\[
 \sum_{P\in\mathcal S_i}\sum_{K\le k<2K} k |A_P(k)-A_{P,u_i}(k)|^2
 \ll K^2U^2\bigl((X/L^{D_0})\rho_i+e^{2L^\delta}\bigr).
\]
Here one \(U\) is from Cauchy, another from the sum over \(p\); \(\sum_k k=O(K^2)\). Summing all slabs and \(O(L)\) blocks gives
\[
 O(X^3L^{\delta-D_0}+X^{2+o(1)}).
\]
The additive \(e^{-cL^\delta}\) is included in the first bound for fixed \(D_0\). Request frozen saving \(N>A+D_0+2\) and take \(D_0>A+2\); \(|x+y|^2\le2|x|^2+2|y|^2\) proves (1).

## 5. Scope and G23 usage

Markov with \(A>F+E\) proves the exception count in §1, including in any given target subfamily that actually contains \(\gg X/L^B\) targets for fixed \(B\) (increase \(F\)). It gives no information for the intended much thinner radical class. Indeed if \(\operatorname{rad}(P)\le L^B\), there are at most \(L^B\) possible radicals; each has \(O_B(\log L)\) distinct primes and each exponent has \(O(L)\) possibilities. Hence the whole class has size at most \(\exp(O_B((\log L)^2))=X^{o(1)}\), and could be entirely exceptional, as could all powers of 2. There is no fixed-\(P\) Chowla or Goldbach consequence.

The genuine unmarked mixed G23 term equals \(-L_P\sum_k R_{z_P}(k)\lambda(k)A_P(k)\), by \(p>z_P\) and complete multiplicativity at each true prime slope. Weighted Cauchy and the elementary \(\sum_k R_{z_P}(k)/k=O(L_P)\) give \(|\mathcal M|^2\ll L_P^3\mathcal Q_P\), so (1) pays this term to every fixed log power outside the stated exception set. It does not pay any other G23 high-term budget.

The true signed coprime off-diagonal is also log-small on the same targets when \(c_p=1\), with both original rough conditions. Subtract the diagonal \(O(P^{2-\sigma})\) and noncoprime part from \(\mathcal Q_P\). For a common prime \(\ell>y_P\) not dividing \(P\), one has \(\ell\mid(p-p')\) and the unique reduced progression \(k\equiv Pp^{-1}\pmod\ell\); on each scale \(p,p'\asymp U,\ k\asymp K,\ U\ll K\), the usual actual weighted count is \(O(U^2K^2/\ell^2)\), with the floors absorbed since \(\ell\ll U\) and \(p\ne p'\). This totals \(O(P^2 L_P/y_P)\). If \(\ell\mid P\), distinct prime slopes force \(\ell\mid k\), hence \(\ell>z_P\). For each such \(\ell\le 2K\), there are \(O(K/\ell)\) multiples in the block, at most \(O(U^2)\) slope pairs and weight \(O(K)\). Summing those target prime factors and blocks adds \(O(P^2L_P^2/z_P)\), since there are \(O(L_P)\) factors. So the coprime conclusion does not require small radical either. Without averaging in \(P\), (5) has no Parseval collapse and [the previously isolated dense two-affine problem](SmallRadicalWeightedCoprimeDispersion.md) is still open.