# The first failure of balanced binomial divisibility

For \(m\ge1\) define
\[
C_m=\binom{2m}{m},\qquad
B(m)=\min\left\{k\ge1:\binom{m+k}{k}\nmid C_m\right\}.
\]
Thus all \(k\le K\) satisfy the divisibility if and only if \(K<B(m)\). The minimum exists because the binomial coefficient on the left tends to infinity for fixed \(m\). This threshold is associated with [Pomerance, *Remarks on the middle binomial coefficient*, Theorem 2](https://math.colgate.edu/~integers/aa47/aa47.pdf) and the balanced family used for [Erdős Problem 728](https://www.erdosproblems.com/728). Pomerance proved the density-one divisibility for all \(k\le \exp(\gamma\sqrt{\log m})\) when \(\gamma<\sqrt{\log 2}\); his final remark leaves the sharp boundary open. [Sothanaphan, arXiv:2601.07421, Corollary 1 and its appendix discussion](https://arxiv.org/pdf/2601.07421) obtains the same subcritical range and gives a missing-prime heuristic for optimality.

We give an exact pointwise formula, identify the source of failures near the transition, and then transfer the sharp density scale from [Eric Li's 2026 preprint on the distinct least-nondivisor question, Erdős Problem 731](https://arxiv.org/abs/2606.29062v1). The formula and the estimates in §§1–2 are independent of that preprint. The distributional statements in §3 invoke its Theorem 1.3, and require only its fixed-\(z\) form.

## 1. A pointwise formula

For prime \(p\), put \(t_p=v_p(m)\) and \(V_p=v_p(C_m)\). Then
\[
\boxed{\ \ 
B(m)=\min_p b_p(m),\qquad
b_p(m)=p^{t_p+V_p+1}-(m\bmod p^{t_p+V_p+1}).
\ \ } \tag{1}
\]
In fact \(b_p(m)\) is the least positive \(k\) for which the \(p\)-adic valuation of \(\binom{m+k}{k}\) exceeds \(V_p\).

By Kummer's theorem, a carry across level \(j\) in adding \(m+k\) occurs precisely when
\((m\bmod p^j)+(k\bmod p^j)\ge p^j\). There is no such carry for \(j\le t_p\). For \(j>t_p\) it requires \(k\ge d_j:=p^j-(m\bmod p^j)\). The \(d_j\) are nondecreasing: if \(a_j\) is the digit of \(m\) at position \(j\), then \(d_{j+1}=d_j+(p-1-a_j)p^j\). Any addition with at least \(V_p+1\) carries therefore has \(k\ge d_{t_p+V_p+1}\). At \(k=d_{t_p+V_p+1}\) we have \(k\equiv -m\bmod p^j\) for all \(j\le t_p+V_p+1\); hence every level \(t_p+1,\ldots,t_p+V_p+1\) does give a carry. This proves (1). The restriction to missing primes is not pointwise true: at \(m=5\) the first failure is \(k=3\), with \(\binom83=56\) and \(v_2(C_5)=2<3=v_2(56)\).

If \(b_p(m)\le K\) then \(p\le 2K\). Indeed otherwise \(m\bmod p^j=p^j-b_p(m)\) for \(j=t_p+V_p+1\) in (1). Its lowest digit is \(p-b_p(m)>p/2\) and the next \(j-1\) digits are \(p-1\). All these digits carry when \(m\) is doubled, implying \(V_p\ge j\), a contradiction. This is the familiar large-prime observation in Pomerance's argument, expressed at the first failure.

## 2. Only missing primes matter near the transition

Take \(m\) uniformly among integers in \([X,2X)\), write \(L=\log X\), \(s=\sqrt{(\log 2)L}\), and let \(K\) be an integer with \(\log K=(1+o(1))s\). Away from a set of relative size \(O(K^{-1/2+o(1)})\), all three properties hold:
1. No prime \(p\) with \(V_p>0\) reaches \(b_p(m)\le K\).
2. A missing prime \(p\le2K\), meaning \(V_p=0\), never divides \(m\).
3. No higher prime power \(p^a\le K\) with \(a\ge2\) fails to divide \(C_m\).

Consequently, if \(B(m)\le K\) on this good set, it equals
\[
\min_{\substack{p\le2K\\p\nmid C_m}}\big(p-(m\bmod p)\big). \tag{2}
\]
For any real \(1\le Y\le K\), let \(A(m)=\min\{a\ge1:a\nmid C_m\}\), the least nondivisor of the single central coefficient. On the same good set,
\[
 A(m)\le Y\ \Longrightarrow\ B(m)\le Y\ \Longrightarrow\ A(m)\le2Y. \tag{3}
\]
For the first implication, \(A(m)\) must be a prime power by unique factorization, and property 3 means here it is prime. By property 2 this prime does not divide \(m\), so (1) gives \(b_p(m)\le p\). For the second implication use (1), property 1 and \(p\le2B(m)\).

### Proof of the exceptional estimate

Let \(P=K^{3/4}\) and \(D_p=\lfloor L/\log p\rfloor\). In an interval of length \(X\), any condition modulo \(p^{D_p}\le X\) has probability at most twice its fraction of residue classes. The first \(D_p\) independent uniform digits give the exact fractions in this comparison. Call a digit high when it is at least \(\lceil p/2\rceil\); every such digit forces an outgoing carry when doubling, regardless of its incoming carry. The fraction of non-high digits is
\(\rho_2=1/2\) at \(p=2\) and \(\rho_p=(p+1)/(2p)\) otherwise. Thus for \(h\le D\) digits, the fraction of strings with at most \(h\) high digits is at most \(\rho_p^D\sum_{j\le h}\binom Dj\), since the high digits are no more numerous than the non-high ones.

For \(p\le P\) set \(H_p=\lfloor D_p/\log D_p\rfloor\). First discard all \(m\) with \(V_p\le H_p\) for some \(p\le P\). The probability summed over such primes is
\[
\ll \sum_{p\le P}\rho_p^{D_p}\exp\big(O(D_p\log\log D_p/\log D_p)\big).
\]
For \(p\le \exp(L^{1/4})\) the sum is \(\exp(-\Omega(L^{3/4}))\), since \(\rho_p\le2/3\) and \(D_p\ge L^{3/4}-1\). For the remaining primes \(p\le P\), \(D_p\ge L/\log P-1\), \(\rho_p=1/2+o(1)\), and the entropy error is \(o(D_p)\), all uniformly. The sum there is at most
\[
\exp\!\left[\left(\tfrac34-\tfrac43+o(1)\right)s\right]
=K^{-7/12+o(1)}.
\]
We also discard \(m\) for which some \(p^{H_p}\) with \(p\le P\) divides any of \(m+1,\ldots,m+K\). The modulus is at most \(X\), and \(H_p\log p\gg L/\log L\) uniformly. A union bound costs at most \(2KP\exp(-c L/\log L)\) for some \(c>0\). The surviving \(m\) cannot have \(b_p(m)\le K\) for small \(p\) by (1). Furthermore \(H_p\log p\gg L/\log L>\log K\), so if \(p^a\le K\) with \(a\ge2\), then \(p\le\sqrt K<P\) and \(V_p>H_p\ge a\). This proves property 3 and handles all small primes in the other two properties.

Now suppose \(P<p\le2K\). Throughout this range,
\[
 D_p=O(s),\qquad
 \rho_p^{D_p-2}\le K^{-1+o(1)}.
\]
The latter follows from \(D_p\ge L/\log(2K)-1\) and \(\log\rho_p=-\log2+O(1/P)\). To have \(b_p(m)\le K\) when \(V_p\ge2\), (1) requires a multiple of \(p^3\) among the next \(K\) integers. Each \(p^3\le X\) for large \(X\), so this costs \(O(K\sum_{p>P}p^{-3})=O(K/P^2)=O(K^{-1/2})\) in total. When \(V_p=1\), (1) requires a multiple of \(p^2\) in the same window. Because \(p^2>K\), this allows only \(K\) residues modulo \(p^2\). Fixing those two lowest digits, the remaining \(D_p-2\) digits can include at most one high digit. Independence of the low and high digit blocks **within a single base** gives the bound
\[
\ll \sum_{P<p\le2K}\frac K{p^2}(D_p+1)\rho_p^{D_p-2}
 \le K^{-3/4+o(1)}.
\]
Finally, \(p\mid m\) and \(V_p=0\) requires the lowest digit to vanish and all others to be non-high, which sums to at most
\(\ll\sum_{P<p\le2K}p^{-1}\rho_p^{D_p-1}\le K^{-1+o(1)}\).
All probabilities here are bounded by the one-base residue counts and union bounds. Together they give the claimed error. On this good set a prime responsible for \(B(m)\le K\) is missing and does not divide \(m\); its quantity in (1) is \(p-(m\bmod p)\). The minimality of \(B(m)\) proves (2).

## 3. Sharp scale for Pomerance's threshold

Let
\[
F(x)=\sqrt2(\log2)^{1/4}(\log x)^{1/4}
     \exp\!\sqrt{(\log2)\log x}.
\]
[Li's Theorem 1.3](https://arxiv.org/pdf/2606.29062v1) proves, for each fixed \(z\ge1\) and all large \(X\), the two-sided order
\(\mathbb P_X(A(m)\le F(2X)e^{-z})\asymp e^{-2z}\) and the upper bound
\(\mathbb P_X(A(m)>F(2X)e^z)\ll e^{-2z}\), with absolute implicit constants. Apply (3) using, for example, \(K=\lfloor e^{s+L^{1/8}}\rfloor\) to cover all these fixed-\(z\) cutoffs. It follows that
\[
\begin{split}
\mathbb P_X(B(m)\le F(2X)e^{-z})&\asymp e^{-2z},\\
\mathbb P_X(B(m)>F(2X)e^z)&\ll e^{-2z}
\end{split} \tag{4}
\]
for each fixed \(z\ge1\) and large \(X\), again with absolute constants. In the lower-tail upper bound use Li at \(z-\log2\), with the trivial probability bound for \(1\le z<1+\log2\). The exceptional set in §2 has probability tending to zero faster than needed for any of these fixed cutoffs. Also, the probability of \(A(m)>K\) tends to zero: for every fixed \(z\), the cutoff \(F(2X)e^z\) is eventually below \(K\), and then the upper-tail bound can be made arbitrarily small by increasing \(z\). Thus (3) gives the explicit coupling \(A(m)/2\le B(m)\le A(m)\) on a set of natural density one.

Summing dyadic blocks gives the density-tight scale
\[
\log B(m)
 =\sqrt{(\log2)\log m}+\tfrac14\log\log m+O_{\rm dens}(1),
\]
where the last term means that the upper density of deviations exceeding \(C\) tends to zero as \(C\to\infty\). Indeed \(F(m)/F(2X)\to1\) uniformly on \([X,2X)\) and the bounds in (4) hold for each fixed \(z\). In particular:
- For every fixed \(\alpha<1/4\), for a density-one set of \(m\) **all** \(k\le(\log m)^\alpha\exp\!\sqrt{(\log2)\log m}\) satisfy the divisibility. This includes Pomerance's endpoint \(\alpha=0\).
- For every fixed \(\alpha>1/4\), the set of \(m\) for which all such \(k\) satisfy it has density zero.
- No positive function \(f\) with \(\sup_{X\le u,v<2X}|\log f(u)-\log f(v)|\to0\) can have \(B(m)/f(m)\to1\) in natural density. To see this, choose two fixed lower-tail cutoffs \(aF(2X)<bF(2X)\) with \(0<a<b\) using (4): the mass below \(aF(2X)\) is bounded below, and the mass above \(bF(2X)\) can be made at least \(3/4\). A center that varies by \(o(1)\) in logarithm on the block cannot approximate both sets multiplicatively.

This proves a sharp density threshold for the balanced divisibility family, not a limiting distribution, an answer for arbitrary \(a,b\), or a new resolution of the original existence question #728. It does not reprove Li's analytic tail theorem. [verify_factor_binomial_first_failure.js](verify_factor_binomial_first_failure.js) is a finite exact check of the nearest-multiple formula and the conditional digit-counting interface.
