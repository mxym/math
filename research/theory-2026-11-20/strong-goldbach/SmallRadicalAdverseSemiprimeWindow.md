# A true adverse semiprime-pair bound from one angular window, including the balanced corner

This is an actual upper bound for a negative part of the shifted high coefficient; it does not use translated or base packet tags. It extends the earlier two-narrow-window affine sieve to one short-prime restriction without losing the near-balanced configurations. No asymptotic for the full dispersed \((2,2)\) class is claimed.

## 1. Result and usable ranges

Let \(P\) be sufficiently large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(y=e^{L^\delta}\) for fixed \(0<\delta<.1\), and \(I=PJ\) for compact interior interval \(J\subset(0,1)\). Let \(\mathcal S\) be **any** set of true primes in \((y,\sqrt P]\). Consider genuine rows
\[
n=pq\in I,\qquad m=P-pq=s r,\qquad P^{1/4}<p<q,\quad y<s<r,\quad s\in\mathcal S,
\tag{1}
\]
with \(p,q,s,r\) all prime. Their signed high weight is \(-\log(pq)\), because \(T(pq)=-\log(pq)\) and \(\lambda(sr)=+1\). For sufficiently large fixed \(K\) all these rows are base-uncovered: \(sr\) has at most two packet factors so cannot meet \(K>2\) distinct base packets. The assertion is about the actual adverse family, not the \(w=1\) row, which is favorable.

Their total absolute negative weight is
\[
W_-(\mathcal S)\ll_{J,B,\delta}\frac{P S(P)}{L}\sum_{s\in\mathcal S}s^{-1}+P^{.83}.
\tag{2}
\]
The same bound holds after any further restriction, such as \(r>P^\rho\), the actual translated selector, all \(s>P^{1/4}\), or selecting only rows in specific source rectangles.

In particular for \(\sum_{s\in\mathcal S}1/s=o(L^{-\delta})\) it pays this negative domain at \(o(PV_y(P)/L)\), where \(V_y(P)\asymp S(P)/L^\delta\). For example:
* A single fixed relative-width shell for \(s\) at any fixed polynomial scale has \(s\)-mass \(O(1/L)\), hence weight \(O(PS(P)/L^2)\), while \(p\) is **not** narrowed. This includes the fully balanced corner \(s\asymp\sqrt P\), even if both products are themselves in balanced prime rectangles.
* For fixed \(\beta>\delta+\varepsilon>0\), \(\beta<1\), the much wider subpolynomial shell \(\log s\in[L^\beta,L^\beta+L^{\beta-\delta-\varepsilon}]\) has reciprocal mass \(O(L^{-\delta-\varepsilon})\) by the prime reciprocal asymptotic with arbitrary-log error at these endpoints. The yield is \(O(PV_y/L^{1+\varepsilon})\), including the near-full \(r\) regime.
* The bound with **all** \((y,\sqrt P]\) allowed into \(\mathcal S\) gives no required saving; even a wide polynomial angular interval has reciprocal mass \(\asymp1\). There is no comparison to an unrelated positive chamber.

## 2. Fixed \(s\) and the exact modular hyperbola with a sieve modulus

Cover the source by \(O(L)\) short-prime boxes. For each, \(p\) ranges over an interval \(I_1\) of fixed small relative width at scale \(X\in[P^{1/4},O(\sqrt P)]\). The resulting possible \(q\)'s lie in an interval \(I_2\) at scale \(Y\asymp_J P/X\) with \(|I_2|\ll_J Y\); take the original \(p\) bins half-open to eliminate repeats. Widening to \(I_1\times I_2\) keeps the product in a slightly larger **fixed interior** interval \(PJ'\subset(0,P)\) by choosing the \(p\)-width sufficiently small. In particular \(X+Y\ll_J P^{.75}\), and \(r=(P-pq)/s\gg_J P/s\) on every counted pair with integer \(r\).

Fix \(s\in\mathcal S\). Then \(s\nmid P\) since \(s>y>\operatorname{rad}(P)\). Retain \(x\in I_1,\ q\in I_2\) with \(xq\equiv P\bmod s\); define the integer \(\widetilde r=(P-xq)/s\). At a further modulus \(d\) coprime to \(s\), \(\widetilde r\bmod d=(P-xq)s^{-1}\bmod d\) exactly, so every local sieve condition on \(x,q,\widetilde r\) is a condition on a **pair** of residues \((x,q)\bmod d\).

For each fixed residue pair \(x\equiv a,\ q\equiv b\bmod d\), we claim the genuine lattice count is
\[
\frac{s-1}{s^2}\frac{|I_1||I_2|}{d^2}
+O\left(\sqrt{s}\log^2(2s)+\frac{|I_1|+|I_2|}{d s}+\frac1s\right).
\tag{3}
\]
Here is the completion including all interval floor terms. The exact numbers of \(x\) and \(q\) in their progressions are \(N_x=|I_1|/d+O(1)\), \(N_q=|I_2|/d+O(1)\). As \(d\) is invertible modulo \(s\), their distributions modulo \(s\) are the sums of \(\lfloor N_x/s\rfloor,\lfloor N_q/s\rfloor\) complete periods and a terminal step-\(d\) progression of length \(<s\) each. In the hyperbola count \(\sum_{t\in\mathbb F_s^\times} A(t)B(P/t)\), the two complete parts give their predicted main term exactly, and the terms with only one residual differ from that main term by \(O((N_x+N_q)/s)\): the missing zero residue in a residual changes its total by at most one relative to the uniform prediction.

For the two residuals, with normalized Fourier transforms, the \(\ell^1\) norm of each transform is \(O(\log(2s))\) by the geometric series for an interval (the unit step \(d\) permutes nonzero frequencies). The zero-zero frequency gives exactly \((s-1)\) times the product of the two normalized lengths. If just one frequency is nonzero, the complete sum over \(t\ne0\) is \(-1\). If both are nonzero, the complete sum is \(\sum_{t\ne0}e_s(h t+kP/t)\), bounded by \(2\sqrt{s}\) by [Weil's Kloosterman bound](https://doi.org/10.1073/pnas.34.5.204). The two-residual error is therefore \(O(\sqrt{s}\log^2(2s))\). Replace \(N_x,N_q\) by the actual interval lengths divided by \(d\) in \((s-1)N_xN_q/s^2\); the last error is \(O((|I_1|+|I_2|)/(ds)+1/s)\). This proves (3), including when \(N_x,N_q\gg s\) or the affine interval obtained by fixing both prime factors would have length \(O(1)\).

## 3. Exact bad-point counts and Selberg denominator

Use sieving primes \(\ell\le W\), \(\ell\ne s\), with \(W=D^\gamma,\ D=P^{1/100}\), and \(\gamma>0\) a sufficiently small fixed constant. True \(x,q,\widetilde r\) in (1) all exceed \(W\). The one additional excluded sieve prime \(\ell=s\), if it is in range, is omitted solely to keep (3) valid and is \(>y\). It need not be larger than \(W\). For each other sieve prime the bad pairs are
\[
x=0\quad\text{or}\quad q=0\quad\text{or}\quad xq=P\pmod\ell .
\]
If \(\ell\nmid P\), the first two lines have union \(2\ell-1\) and the nonzero hyperbola has \(\ell-1\) more points. If \(\ell\mid P\), the hyperbola equals the union of the two lines. Thus the precise bad count is \(\nu(\ell)=3\ell-2\) or \(2\ell-1\), respectively. In particular at the even target's \(\ell=2\), it is \(3<4\).

For squarefree \(d\) on the sieve primes, its simultaneous bad-pair set has cardinality \(\nu(d)=\prod_{\ell\mid d}\nu(\ell)\) by CRT on the two coordinate lists, and density \(g(d)=\nu(d)/d^2\). Summing (3) over exactly these pairs gives
\[
\frac{s-1}{s^2}|I_1||I_2|\,g(d)
+O\left(d^2\sqrt s\,\log^2(2s)+d\,(|I_1|+|I_2|)/s\right).
\tag{4}
\]
The remainder uses only the exact residue count bound \(\nu(d)\le d^2\), so there is no hidden tuple or divisor-weight estimate. This remains true with CRT's natural lexicographic listing; no choice of residues depends on a period representative.

Apply the elementary Selberg square with weights \(\lambda_d=0\) unless \(d\le D\) is supported on these sieve primes, \(\lambda_1=1\), and \(|\lambda_d|\le1\). For completeness, the finite diagonalization in the prior natural-scale note applies to this \(g\) verbatim, giving its main quadratic form \(1/G(D)\) for \(G(D)=\sum_{d\le D}\prod_{\ell\mid d}g(\ell)/(1-g(\ell))\). A normalized full product on these divisors includes a prime independently with probability \(g(\ell)\le3/\ell\), so its expected log size is \(\ll\log W\). Taking \(\gamma\) small enough, at least half its mass has \(d\le D\) by Markov. Thus \(1/G(D)\ll\prod_{\ell\le W,\ell\ne s}(1-g(\ell))\). At prime \(\ell\) the good density is
\[
1-g(\ell)=
\begin{cases}
(1-1/\ell)(1-2/\ell),&\ell\nmid P,\\
(1-1/\ell)^2,&\ell\mid P.
\end{cases}
\]
Divide by \((1-1/\ell)^3\) to get the standard singular factors; all target primes are below \(W\), the tail is absolutely convergent, and omitting \(s>y\) costs \(1+O(1/y)\). The sieve main is therefore \(O(PS(P)/(sL^3))\) in this entire source box.

In the error from (4) take \(d=[d_1,d_2]\le D^2\) for each of at most \(D^2\) ordered pairs. The explicit total is
\[
O\left(D^6\sqrt s\,L^2+D^4(X+Y)/s\right).
\tag{5}
\]
No use of \(\tau(d)\) or pointwise error amplification beyond these crude exponents is needed. Summing over the actual \(s\in\mathcal S\), \(\sum_{s\le\sqrt P}\sqrt s\ll P^{3/4}\) even over integers, and \(\sum_{s\in\mathcal S}1/s\ll\log L\) by the prime harmonic bound. Thus (5) contributes \(O(P^{.81+o(1)})\) per source box. The harmless replacements \(P/s\) by \((s-1)P/s^2\), and Fourier floors, were already included in (3)–(4).

Finally there are \(O(L)\) source boxes and the genuine source weight is at most \(L\). Multiplying the main/total errors gives (2), with ample power room in the latter. Since any actual selector is 0 or 1 after normalization, the same charged upper bound applies to its selected negative rows. This is a direct joint bound for one adverse domain; in particular no cancellation is claimed for broad dispersed semiprime-pair mass when the harmonic size condition fails.
