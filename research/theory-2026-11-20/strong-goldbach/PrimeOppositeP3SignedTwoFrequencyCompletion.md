# Signed two-frequency completion for the true middle P3 remainder

Written follow-up, 2026-11-24, to [the actual q-Poisson remainder](PrimeOppositeMiddleJointPoissonWeil.md) and the later [actual-LCM barrier](PrimeOppositeActualLCMSupportBarrier.md). This is a signed reduction and several genuinely paid subfamilies of its completed off-diagonal, not a new bound for its remaining oscillatory part or a P3 theorem.

Fix \(N=2^k\) (the calculation also works for general even \(N\) on the same unit support), \(H=\sqrt N\), and \(r\asymp R,s\asymp S,q\asymp Q\). Let \(q\) be a true prime not dividing \(N\). Let \(s\) be squarefree, \((s,N)=1\), and \(S<Q\) with a fixed exponent margin. Keep \((r,qs)=1\) in the true Poisson sum. Suppose \(R\ll SQ^2\), the Fourier length \(A_0=RQS/H\) is small enough that \(N^\epsilon(1+A_0)<Q\) for a fixed \(\epsilon>0\), and smooth amplitudes at polynomial scale have logarithmic derivative growth as in the originating note. Write \(b_{q,s}\) for the actual \(q\)-coefficients, with \(|b_{q,s}|\le1\), independent of \(r\), not necessarily nonnegative or independent of \(s\).

With \(W\) the smooth source window, put
\[
 a_{q,h,s}(v)=\frac{H}{Rvqs}\widehat W\!\left(\frac{Hh}{Rvqs}\right).
\]
After the exact switched Poisson formula, \(E(r,s)\) is the sum over \(q,h\ne0\) of \(b_{q,s}a_{q,h,s}(r/R)e(hN\bar r/(qs))\) with the said \(r\)-unit condition. The negligible Fourier tails may be excised in every expression below; the retained \(h\) satisfy \(0<|h|<q\). Choose one nonnegative smooth fixed \(\psi(v)\ge1\) on the physical \(r/R\) block, compactly supported in a fixed interior positive interval. Cauchy gives
\[
 \sum_{s}\sum_{r\text{ in block}} |E(r,s)|
 \ll (RS)^{1/2}\biggl(\sum_s\sum_r \psi(r/R)|E(r,s)|^2\biggr)^{1/2}.
 \tag{1}
\]
In contrast to the previous q-only Cauchy, *retain both real Poisson modes in this square, and retain the signs of the actual q-coefficients and of the completed kernels*. Define
\[
 \begin{split}
 m&=s q_1q_2,\quad A=N(h_1q_2-h_2q_1),\\
 G_{12,s}(v)&=\psi(v)a_{q_1,h_1,s}(v)\overline{a_{q_2,h_2,s}(v)},\\
 \operatorname{Kl}_m(A,\ell)&=\sum_{\substack{u\bmod m\\(u,m)=1}}
                          e\bigl((A\bar u+\ell u)/m\bigr).
 \end{split}
\]
For \(q_1\ne q_2\), CRT makes the product of the two actual Poisson inverse phases \(e(A\bar r/m)\). Completing \(r\) in its residue classes gives the exact signed contribution of this pair:
\[
 b_{q_1,s}\overline{b_{q_2,s}}\frac Rm
 \sum_{\ell\in\mathbb Z}\widehat G_{12,s}(\ell R/m)
             \operatorname{Kl}_m(A,\ell).
 \tag{2}
\]
The ordered sum over \(s,q_1\ne q_2,h_1,h_2,\ell\) is real by swapping both pairs and negating \(\ell\); no absolute values across these coordinates are logically required. The formula uses the original \(N\), including its exact size in each Kloosterman argument, not a shifted small residue. Direct completion of the smooth product keeps the actual signed Fourier weights without a separation claim.

For clarity, neither \(q_i\) divides \(A\): for \(i=1\), \(A\equiv N h_1q_2\pmod {q_1}\), and analogously \(-N h_2q_1\) at \(q_2\). The \(q_1,q_2\) Kloosterman factors in (2), with \( \operatorname{Kl}_q(1,\cdot)\) normalization, have arguments
\[
 Nh_1\ell\,\overline{s^2 q_2} \pmod{q_1},
 \qquad -Nh_2\ell\,\overline{s^2 q_1} \pmod{q_2}.
\]
The \(s\) factor has arguments \(N(h_1\bar q_1-h_2\bar q_2)\) and \(\ell\overline{q_1q_2}\) modulo \(s\), retaining the exact possible nonunits. Thus the two Kloosterman prime factors see independently varying \(h_1,h_2\), not the single \(h\) of the old off-diagonal estimate.

## Parts already paid

For each fixed \(J>0\), mixed smooth weights and integration by parts give
\[
 |\widehat G_{12,s}(\xi)|\ll_J L^{O_J(1)} w_J(h_1)w_J(h_2)(1+|\xi|)^{-J},\qquad
 w_J(h)=A_0^{-1}(1+|h|/A_0)^{-J}.
\]
For \(e\ge1\), monotone integral comparison on nonzero multiples gives
\(\sum_{h\ne0,e\mid h} w_J(h)\ll 1/e\); if the sum is restricted to \(0<|h|\le A_0 S^{-\gamma}\), it is instead \(\ll S^{-\gamma}/e\). The same bounds apply to dual \(\ell\) with \(A_0\) replaced by \(m/R\), after normalization by \(R/m\). They remain valid if the short ranges contain no integers, and are uniform since \(m\asymp SQ^2\).

The same-\(q\) energy, allowing all \(h_1,h_2\), is \(O(RQS L^C)\): for each \(q,r,s\) sum the two absolute rapid amplitudes separately before squaring. For \(q_1\ne q_2\) and \(\ell=0\), the complete factor is a Ramanujan sum; each \(q_i\)-local value is \(-1\), and the \(s\)-local size is at most \(s\). Summing the absolute completed weights shows \(O(RS L^C)\) for all these zero modes together.

For nonzero \(\ell\), Weil and CRT give
\[
 |\operatorname{Kl}_m(A,\ell)|\ll N^{o(1)}Q\sqrt s\,\sqrt{(s,h_1q_2-h_2q_1,\ell)}.
\]
Here a joint congruence improves over discarding \(\ell\) from the gcd. For every squarefree \(d\mid s\), the normalized h-weighted number of pairs of true primes with \(d\mid h_1q_2-h_2q_1\) is \(\ll N^{o(1)}Q^2/d\). Indeed fix \(h_1,h_2\), remove \(e=(d,h_1,h_2)\), and use that \(q_i\) are units modulo \(d\). If just one \(h_i/e\) is a nonunit at any prime of \(d/e\), there are no pairs. Otherwise fixed \(q_1\) leaves exactly one reduced class for \(q_2\) modulo \(d/e\), containing \(O(Qe/d+1)\) possible integers; since \(d\le S<Q\), \(1\) is absorbed. The weighted average of \(e\) is \(O(N^{o(1)})\), by replacing \(e\) by \(\sum_{a\mid d,a\mid h_1,a\mid h_2}a\) and using the weighted multiple count \(O(1/a)\) twice. The proof also shows the bound gains a factor \(S^{-\gamma}\) if one of the two \(h_i\) is in that short range. Prime unit conditions are exact, while counting integers in the residual class is only an upper.

Since \(\sqrt{g}\le\sum_{d\mid g}\sqrt d\), the dual multiple bound and the preceding congruence bound give divisor weight \(d^{-3/2}\) after summing nonzero \(\ell\) and the normalized \(q,h_1,h_2\) weights. This proves the old absolute off-diagonal total \(O(Q^3 S^{3/2}N^{o(1)})\) in the new completed coordinates. It also rigorously pays each of these subfamilies at \(O(Q^3 S^{.8}N^{o(1)})\):
* \(0<|\ell|\le(m/R)S^{-.7}\), by the shortened dual-multiple count.
* \(0<|h_i|\le A_0 S^{-.7}\) for at least one \(i\), by the shortened \(h_i\)-multiple count.
* The triple gcd \(g=(s,h_1q_2-h_2q_1,\ell)>S^{7/15}\). In this case use only \(d>S^{7/15}\) in the majorization of \(\sqrt g\), which is still valid by taking the divisor \(d=g\); the divisor weight is at most \(S^{-.7+o(1)}\).
If desired the same threshold pays either single gcd \((s,h_1q_2-h_2q_1)>S^{.7}\) or \((s,\ell)>S^{.7}\) by introducing the large divisor \(c\mid s\) in the corresponding congruence, replacing one \(1/d\) probability by \(1/[c,d]\le1/c\), and summing \(\sum_d d^{-1/2}\ll s^{o(1)}\). This retains the additional \(S^{-.7}\) loss. Overlapping paid cases can simply be partitioned; no cancellation is claimed on them.

## Exact one-sided remaining target

With all the paid pieces removed, it suffices to bound the remaining **signed** completed sum (2) above by \(Q^3 S^{.8}N^{o(1)}\), or any comparable upper of that size after a finite dyadic partition. By (1) it would give
\[
 \sum_{s}\sum_{r}|E(r,s)|
   \ll N^{o(1)}\bigl(R S Q^{1/2}+R^{1/2}Q^{3/2} S^{.9}\bigr).
\]
This is precisely the support-domain threshold for the genuine .06 strip improvement in the [safe-shape note](PrimeOppositeP3SafeShapeBarrier.md). It suffices to bound the real signed \(s,q_1,q_2,h_1,h_2,\ell\) total: separate square-root cancellation for each \(s\), each pair of \(q\)'s, each frequency, or each positive/negative coefficient is not required. The statements proved here do not bound the surviving full-size, mostly unit dual modes by that target and do not change the current global P3 status. They give the exact dual signed weights and isolate the subfamilies that need no new cancellation.