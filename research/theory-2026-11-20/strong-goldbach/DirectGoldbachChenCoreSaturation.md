# Almost-all saturation of the two weighted Chen semiprime cores

This gives an unconditional obstruction to the two **universal** core caps in the [weighted semiprime discriminator](DirectGoldbachRepairedChenSemiprimeDiscriminator.md). It counts genuine primes and semiprimes, not formal densities, and does not use the transferred Li numerical sieve estimates. It does not rule out a bound conditioned on the actual prime-pair count being deficient.

Let \(\mathfrak S(N)\) be the ordered binary Goldbach singular series and \(X_N=\mathfrak S(N)N/(\log N)^2\). Write
\[
 H_c(N)=\sum_{\substack{p+s r=N\\p,s,r\text{ prime},\,s<r}}c(\log_N s).
\]
The two core weights \(c_W,c_C\) both vanish at and above \(0.49\). Below this cutoff \(c_W\) is the piecewise constant \(W\) of the earlier note, and \(c_C\) has value \(1/2\) on \([.102,1/3)\), value \(1\) on \([1/3,.49)\), and zero elsewhere. If the earlier boundary trimming is imposed on \(p,sr\), the following conclusion is unchanged. For every fixed \(A>0\), outside \(O_A(X/(\log X)^A)\) even integers \(N\in[X,2X]\),
\[
 H_c(N)=(I_c+o(1))X_N,\qquad
 I_c=\int_0^{.49}\frac{c(t)}{t(1-t)}\,dt .
\]
In particular \(I_W=1.421763588\ldots\), \(I_C=1.394166883\ldots\) by the elementary antiderivative \(\log(t/(1-t))\). The constants are far larger than the proposed caps \(0.6199\) and \(0.095\).

## Freeze the angular endpoints on a dyad

Put \(L=\log X\), \(Y=X/L^{10}\) and initially retain \(p,m=sr\ge Y\). The cost per target is \(O(Y)\), since \(p\) determines \(m\), and a semiprime has a unique ordered decomposition with \(s<r\). For each prime \(s\) form \(b_\pm(s)\) as the supremum/infimum of \(c(\log_V s)\) over \(V\in[X,2X]\). These weights are supported on \(X^{.087}\le s\le(2X)^{.49}\), so \(s^2<Y\) eventually, and every product \(m\ge Y\) occurring has \(r>s\). The frozen lower and upper convolutions sandwich the trimmed \(H_c\). The step endpoints differ from those obtained using \(V=X\) only in a finite number of fixed-ratio prime intervals. The harmonic prime mass of each such interval is \(O(1/L)\), by the prime number theorem. Define continuous densities
\[
 f(u)=\frac{\mathbf1_{[Y,2X]}(u)}{\log u},\quad
 g_\pm(u)=\mathbf1_{[Y,2X]}(u)\sum_s\frac{b_\pm(s)}{s\log(u/s)}.
\]
On their common support \(f=(1+o(1))/L\) and \(g_\pm=(I_c+o(1))/L\) uniformly: replace \(\log(u/s)\) by \(L(1-\log_X s)+O(\log L)\) and apply the harmonic PNT on the fixed exponent intervals. Their bounded-variation norms are \(O(1/L)\), including the two endpoint jumps. Thus \((f*g_\pm)(N)=(I_c+o(1))N/L^2\) uniformly on the dyad.

## Major arcs

Use \(P=L^D\) with \(D\) a sufficiently large fixed constant, arcs \(\alpha=a/d+\beta\) with \(d\le P\), \((a,d)=1\), \(|\beta|\le2P/X\). Let \(F(\alpha)=\sum_{Y\le p\le2X}e(\alpha p)\) and \(G_\pm(\alpha)=\sum_{Y\le sr\le2X}b_\pm(s)e(\alpha sr)\) with both \(s,r\) prime. Siegel–Walfisz and partial summation approximate these by \(\mu(d)\widehat f(\beta)/\varphi(d)\) and \(\mu(d)\widehat g_\pm(\beta)/\varphi(d)\), with kernel sign \(\widehat f(\beta)=\int f(u)e(\beta u)\,du\). Each error is \(O(XL^{-M})\) for any fixed \(M\) on these arcs. For \(G_\pm\), apply Siegel–Walfisz in \(r\in[Y/s,2X/s]\) separately for each \(s\); every \(s\) is coprime to \(d\), so multiplication by \(s\) permutes units, giving the same Ramanujan numerator. Also all \(r> s> d\). The phase multiplier costs \(O(1+P)\) in partial summation and the sum over \(s\) costs at most a bounded harmonic factor. The modulus restriction is a fixed log power in the \(r\) scale also, since \(Y/s\ge X^{.51-o(1)}\). With \(M\) large the integrated product approximation error is negligible, using total major arc measure \(O(P^3/X)\) and the elementary \(O(X)\) bounds for \(F,G_\pm\).

The transforms decay as \(O(1/(L|\beta|))\) by BV, so extending the product integral to all real \(\beta\) costs \(O(X/(PL^2))\) before the Ramanujan coefficient at each rational. Summing the absolute costs uses \(\sum_{d\le P}\mu^2(d)/\varphi(d)\ll \log^C P\) for an absolute \(C\), e.g. by the Euler product over primes at most \(P\). Hence the main is the stated convolution times the truncated series
\[
 \mathfrak S_P(N)=\sum_{d\le P}\frac{\mu^2(d)c_d(N)}{\varphi(d)^2}
\]
with \(c_d\) the Ramanujan sum. The absolute tail summed over \(N\le2X\) is \(O(XP^{-1/2})\): use \(\sum_{N\le2X}|c_d(N)|\le2X\tau(d)\), from its divisor formula, and \(\sum_{d>P}\tau(d)/\varphi(d)^2\ll P^{-1/2}\). The latter follows by inserting \(d^{1/2}/P^{1/2}\) and summing the resulting convergent multiplicative series. Markov bounds exceptions to \(|\mathfrak S(N)-\mathfrak S_P(N)|\le L^{-1}\) by \(O(X L P^{-1/2})\).

## Minor arcs and conclusion

On the complement, Dirichlet approximation with denominator cutoff \(\lfloor X/P\rfloor\) gives \(P<d\le X/P\) with \(|\alpha-a/d|\le d^{-2}\). This yields \(\sup_{\rm minor}|F|\ll X L^{-M'}\) with arbitrarily prescribed \(M'\) by making \(D\) large enough. Indeed use Vaughan's classical prime exponential-sum estimate (R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Theorem 3.1) at endpoints \(Y\le u\le2X\), in the form \(O((u/\sqrt d+u^{4/5}+\sqrt{ud})\log^4(2u))\) for the von Mangoldt sum, remove prime powers and use partial summation. The factor-of-two major-arc width absorbs the rounding of the Dirichlet cutoff. Moreover \(\|G_\pm\|_2^2\le 2X\) by uniqueness of the relevant prime factorization and \(0\le b_\pm\le1\). Bessel on the minor part of \(F G_\pm\) then bounds the number of target coefficients exceeding \(X/L^3\) in absolute value by \(O(X L^{6-2M'})\).

Choose \(D\) for the requested exceptional exponent, then choose the power in Siegel–Walfisz for these arcs. On the nonexceptional even targets the frozen upper and lower convolutions have the same main term, and \(O(Y)\) is negligible because \(\mathfrak S(N)\) is bounded below on the evens. Later movement of any boundary from \(Y\) to \(N/(\log N)^{A_0}\) for fixed \(A_0>2\) again counts only \(o(X_N)\) integers. This proves the claim.

If \(d\le L^B\) and the residue class admits even integers, the class contains \(\gg X/d\) even members of the dyad. With \(A>B+1\), the total exception bound gives relative density \(1-o(1)\) of members exceeding **either** proposed cap, uniformly in the class. Thus adding a fixed or polylogarithmic target congruence cannot make a universal purely semiprime upper at these thresholds true. What remains logically possible is a coupled inequality that applies only when the actual prime-pair contribution is too small.
