# A sign-compatible short-prime coefficient and its true mixed-parity bound under base cover

Research note, 2026-11-24. This is a genuine mixed \(\lambda(n)\lambda(P-n)\) estimate with a short-prime divisor marker on the true base-covered set. It does not control the genuinely base-uncovered polynomial A2/A3 core. The ordinary marked Type I and the mixed projected comparison are separate inputs.

## 1. The short-prime marker and precise result

Let \(P\) be large even with \(\operatorname{rad}(P)\le L^B,\ L=\log P\); let \(I=PJ\) with \(J\) fixed compact interior, \(m=P-n\), \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\), and \(R_t(a)=1_{P^-(a)>t}\). Fix \(0<\sigma<1/4\), \(H=L^{3/5}\), \(D=P^{1/2}e^{-H}\), and let \(\mathcal S\) be any subset of genuine primes in \((P^\sigma,D]\). Define
\[
s(n)=\sum_{\substack{p\in\mathcal S\\p\mid n}}1,\qquad
G(n)=1-\sum_{\substack{p\in\mathcal S\\p\mid n}}\frac{1-\lambda(n/p)}2
    =1-\tfrac12s(n)-\tfrac12s(n)\lambda(n).
\tag{1}
\]
The latter identity uses complete multiplicativity and \(\lambda(p)=-1\); neither \(n\) squarefree nor distinctness of \(p\) in the quotient is required. The count \(s(n)\le 1/\sigma\) uniformly on \(n\le P\). On a true prime \(n\in I\), \(G(n)=1\). On an odd-Liouville \(n\) it is always 1; on positive-Liouville \(n\) it is \(1-s(n)\). For the full \(\mathcal S\), on all-large \(A_2\) with short factor \(p\le D\) and long factor \(q>D\), it is zero.

Let \(C_1(n)\) be the first-cover indicator for actual \(m=P-n\) on the full packet grid, with all admissible even \(K\)-families as in the verified first-cover theorem. Let \(C_{>1}(n)\) be the **separate** actual translated first-cover indicator across \(j=2,\ldots,M+1\) with fixed \(M\). Then for every fixed requested \(A\), choosing sufficiently large fixed even base \(K\), uniformly over \(\mathcal S\),
\[
\begin{aligned}
\sum_{n\in I} C_1(n)R_z(n)R_y(m)(\log n)s(n)\lambda(n)\lambda(m)&=O_A(PL^{-A}),\\
\sum_{n\in I} C_1(n)R_z(n)R_y(m)(\log n)G(n)\lambda(m)&=O_A(PL^{-A}).
\end{aligned}
\tag{2}
\]
The first is the mixed contribution only. The second is the **entire first coefficient** \(G\) on the base-covered portion, not the entire prime target or the high coefficient (which remains). The second also holds with the additional true \(C_{>1}\) mark at an extra absolute loss
\[
O\big(P V_y(P)L^{.76-M/200}+P^{.12}\big),
\tag{3}
\]
which is \(o(PV_y(P)/L)\) for fixed \(M\ge400\). The first estimate admits the same extension. Here \(V_y(P)=\prod_{\ell\le y,\ell\nmid P}(1-1/(\ell-1))\).

## 2. Why the exact mixed weight really has the projected one-variable residual

On each term in \(s(n)\), write \(n=p k\) with \(p\in\mathcal S\). Then \(\lambda(n)=-\lambda(k)\), \(R_z(n)=R_z(k)\), and \(p\) is a target unit since it is polynomial and \(\operatorname{rad}(P)\le L^B\). This provides the two original projected variables **\(p\) and \(k\)**. Both are polynomial: \(p\ge P^\sigma\), \(p\le D\), \(k\asymp_J P/p\). The first factor has bounded (or \(O(L)\)) coefficient supported on true \(p\in\mathcal S\); the specially cancelling second factor is \(\lambda(k)R_z(k)\), possibly multiplied by \(\log k\).

In [the small-radical projected argument](small_radical_projection/Proof.md), §1 (6)–(7) and §2 (12)–(14), the major argument for the \(\mu(k)R_z(k)\) slot uses a uniform arbitrary-log individual character bound on polynomial-length subintervals, including its required low-modulus lifts and the bounded-log Mellin twists, with the other slot still arbitrary bounded-polylog. On the actual support,
\[
|\lambda(k)R_z(k)-\mu(k)R_z(k)|\le 1_{\{k\ {\rm squareful},\,P^-(k)>z\}}.
\]
For any dyadic polynomial endpoint \(X\), the right side has sum \(O(X/z)\), since a squared prime \(>z\) divides \(k\) and \(\sum_{\ell>z}1/\ell^2\ll z^{-1}\). This proves the same uniform individual bound for the **true** \(\lambda(k)R_z(k)\) slot, for all the actual character and twist tests (their modulus is one in absolute value). The \(\log k\) version follows by partial summation with at most a further fixed log loss. We have not assumed such a bound for arbitrary weights replacing the special slot. The minor comparison keeps the same target-unit rough supports and same two-variable size range. Split \(\log n=\log p+\log k\) into its two allowed factors.

For a fixed admissible family \(\mathcal H\), insert its true base tag \(u\mid m\), so the projected equation is
\[
P-pk=u h,\qquad h=m/u .
\]
Outside the packet-square exception, the actual occupancy vector of \(m\) is \(\mathbf c(h)+\mathbf 1_{\mathcal H}\). Define the first-family weight \(A_{\mathcal H}(h)\in[0,1]\) to be the reciprocal of the precise number of tags for that first family, and zero unless \(\mathcal H\) is first for this recovered vector. Hence it is a function of \(h\) (its packet part) alone and not of the actual tag \(u\). Also \(R_y(uh)=R_y(h)\) and \(\lambda(uh)=\lambda(h)\), as the \(K\) tag primes are above \(y\) and \(K\) is even. The exact projected residual is thus
\[
b_{\mathcal H}(h)=A_{\mathcal H}(h)R_y(h)\lambda(h)
\]
with the target-unit filter if retained; all of it is a single bounded function of \(h\). Tag-square exceptions among \(m\le P\) are \(O(Pe^{-L^{.105}})\) integers, and even across all families and tags each such row has at most \(O_K((\log L)^K L^K)\) multiplicity, times bounded \(s\) and one log. Thus extending the one-variable selector formula analytically and then correcting the true exceptional rows is harmless.

For each source/product and tag shell, [the reflected minor comparison](target_slope_switch/Proof.md) and the preceding major bound followed by Cauchy gives arbitrary-log saving, by choosing the fixed even \(K\) with sufficient slack for prime weights, log factors and shells. To handle exactly \(pk\in I\), one may partition the polynomial source scales into boxes of ratio \(1+L^{-C_0}\), keep those wholly within \(I\), and discard the boundary term \(O(P L^{1-C_0})\): only \(O(P L^{-C_0}+1)\) integer \(n\) are near the two endpoints and \(s(n)\le1/\sigma\); the same holds with the actual base mark. Each small box is covered by the comparison's standard relative-width boxes and the needed zero cutoffs, with unrestricted subinterval supports. The number is a fixed power of \(L\), so request more analytic saving before fixing \(K\). The number of families is at most \(O_K((\log L)^K)\) and costs at most one further fixed log power eventually. This proves the first line of (2). An equation with translated tag \(u'\mid jP-n\) instead gives \(\lambda(u'h'-(j-1)P)\); it is not the same \(h\)-only residual and was not used here.

## 3. The linear terms really are Type I on this same base-covered domain

To prove the second line of (2), the additional linear term from (1) has coefficient \(1-s(n)/2\) and one reflected sign \(\lambda(m)\). Write \(n=d k\) with \(d=1\) or \(d=p\in\mathcal S\), then sum \(\log d+\log k\). This is a short divisor \(d\le D\) with bounded coefficient, but one must also justify the exact \(C_1\) mark on the same rows.

For each base family and \(u\mid m\), again \(h=m/u\); let \(a\) be its complete part supported on all packet primes. After the same square exception, \(A_{\mathcal H}(h)\) is determined by \(a\) alone. Truncate \(a\le\exp(L^{.27})\) by the standard Rankin argument in [the first-cover note](SmallRadicalFirstTagCover.md); here it is also an actual divisor of \(m\), and its exponentially small integer exceptional mass may be weighted by the extra divisor sums using fixed moments. Write \(h=a b_0\), require \(b_0\) to have no packet primes, and retain \(R_y(b_0)\) since all \(a,u\) primes exceed \(y\). Open these two roughness restrictions on \(b_0\) at factorial Bonferroni depth \(O_A(\log L)\), with retained squarefree small product \(v\mid b_0\), and put \(b_0=v b\). There is no need to assume \(a,v\) or \(u,a\) coprime; the actual combined factor is \(u a v\) and \(\lambda\) is completely multiplicative. Keep actual target-unit support (valid since \(y>\operatorname{rad}(P)\)). Similarly open source \(R_z(k)\) with a squarefree product \(e\mid k\). In every nonempty tuple \((de,uav)=1\), since a common prime divides \(n,m\) and hence \(P\), contradicting the retained target-unit support. The true progression for the last variable is
\[
b\equiv P(u a v)^{-1}\pmod{de},
\]
with the same target-unit CRT restriction. A profile divisor repeated in \(a v\) is kept with its actual multiplicity; no false CRT independence within that product is needed.

For fixed \(u,a,v\), the actual endpoint is \(P/(u a v)\); the auxiliary logs are \(O(L^{.27}+L^{.24}\log L)=o(H)\) and the entire modulus is \(de\,\operatorname{rad}(P)\le P^{1/2}e^{-H+o(H)}\). This lies in the full weighted maximal Liouville BV range at that endpoint, as in [the near-square-root source calculation](SmallRadicalShiftedHighChambers.md). The \(d\) and the \(e\) are distinguished by prime ranges, so there is no new multiplicity; fixed CRT unit variants cost only log powers. Use \(\log k=\log(P-u a v b)-\log d\) for partial summation at the real endpoints. Sum by \(\sum_{u,a,v}1/(u a v)\) (fixed \(\mathcal V\) times fixed log powers). For every Bonferroni omitted shell the absolute count is \(O(P/(u a v d e)+1)\), using the proved coprimality and exact \(u a v\) product, so factorial reciprocal tails and a \(P^{1/2+o(1)}\) floor bill are valid. All expansion errors are arbitrary-log small. This proves the linear Type I part, and thus the full second estimate in (2).

In particular, on the stated base-covered rows the exact prime identity with \(T_G(n)=-\log n\,G(n)1_{n\ {\rm composite}}\) gives a checked alternative decomposition, since all central true primes have \(G=1\). It pays the **first** coefficient, not the remaining high sum \(\sum T_G(n)\lambda(m)\).

## 4. The actual selector loses absolute weight only; the remaining base miss is real

Both \(s,G\) are bounded in absolute value by constants depending on \(\sigma\) on \(n\le P\). Thus to add the actual translated mark it is enough to upper bound the entirely unsigned true integers with \(R_z(n)R_y(m)=1\) and \(C_{>1}(n)=0\). Baseline sieving in the single variable \(n\) excludes \(0,P\pmod\ell\) at \(\ell\le y\) (these coincide exactly at target divisors), and excludes just \(0\) for \(y<\ell\le z\). All packet primes lie in the latter range. For a greedy witness of noncoverage at all \(M\) offsets, additionally exclude \(jP\bmod\ell\) at its prescribed packet slots. These are all distinct and nonzero mod each such \(\ell\), since \(\ell>M+1\) and \(\ell\nmid P\). The baseline product is exactly
\[
\kappa_z V_y(P),\qquad \kappa_z=\prod_{\ell\le z}(1-1/\ell)\asymp L^{-.24}.
\]
The extra packet ratios have relative product at most \(e^{-\sum_i t_i/4}\), where \(t_i\) is the number of forced offsets at packet \(i\). This gives relative \(L^{-M/200}\) after the usual fixed greedy-witness union with strict exponent margin. These integer counts are valid via elementary Selberg square level \(P^{1/40}\) on all primes \(\le z\): normalized expected divisor log \(O_M(\log z)=o(\log P)\) gives denominator comparison by Markov, and floor \(O(P^{.1})\) per witness. Multiply by \(\log n\ll L\) and absorb witness floors to obtain (3). No independence or cancellation of \(\lambda\) with the selector was used. Analogously, for \((1-C_1)\) alone the greedy exclusions are the single actual root \(P\bmod\ell\) at packet primes; the analogous absolute bound is only \(O(PV_y L^{.76-1/200}+P^{.12})\). It does not pay the uncovered mixed term.

If the full \(G\) decomposition held outside base cover, same-sign orientations would have the desired joint sign on their overlapping main sectors: even \(n,m\) with \(s(n),s(m)\ge1\) make the paired high score nonnegative, and odd/odd composite pairs are always nonnegative. Opposite parity need not be benign in this new decomposition and are **not** asserted to cancel. The polynomial rank-two or rank-three cores with fewer than \(K\) packet primes are base-uncovered. Neither this mixed covered estimate nor the full linear Type I addresses them.
