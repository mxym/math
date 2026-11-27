# A sharp joint uniformity threshold for fixed-weight signed noise

A fixed-weight ternary polynomial can have individually nearly uniform residue coordinates while a collection of those coordinates is far from jointly uniform. In the full-order negacyclic model below, the weight-to-output-dimension threshold can be located exactly. The result compares a standalone, publicly specified probability law to uniformity; it does not analyze a secret-dependent transcript or a concrete cryptosystem.

## 1. Model and result

Let \(q=p^f\) be an odd prime power, \(d=(q-1)/2\), and let \(g\) generate \(\mathbb F_q^\times\). Fix \(\ell\ge2\) with \(\ell\le d\). Take a polynomial
\[
 C(Y)=\sum_{j=0}^{d-1} A_jY^j
\]
uniformly among the coefficient vectors in \(\{-1,0,1\}^d\) with exactly \(k\) nonzero entries, \(1\le k\le d\). Let \(J=\{1,3,\ldots,2\ell-1\}\) and let \(P_{q,k}\) be the law of \((C(g^e))_{e\in J}\). These are distinct linear residue coordinates of \(\mathbb F_q[Y]/(Y^d+1)\).

For small characteristic define \(E=\{e\in J:p\nmid e\}\), \(r=|E|\), and let \(H\subseteq\mathbb F_q^J\) be the graph specified by \(z_e=z_{e/p}^{p}\) for all \(e\in J\) divisible by \(p\). Projection on \(E\) bijects \(H\) with \(\mathbb F_q^r\). The law \(P_{q,k}\) is supported on \(H\). Write \(U_H\) for the uniform law on \(H\). Then, for fixed \(\ell\), the following hold:

1. For every \(k\le r\),
   \[
   d_{\rm TV}(P_{q,k},U_H)\ \ge\ 1-\frac{2^k\binom{d}{k}}{q^r}.
   \]
   Equality holds whenever \(p>2k-1\). In particular, if \(p>2\ell-1\), then \(r=\ell\) and the displayed formula is exact throughout \(k\le\ell\).
2. For each fixed \(k\), the bound for \(k>r\) is
   \[
   d_{\rm TV}(P_{q,k},U_H)=O_{\ell,k}\!\left(q^{(r-k)/2}\right).
   \]
   Moreover, as \(q\to\infty\) over odd prime powers, the entire range \(r+1\le k\le d\) satisfies
   \[
   d_{\rm TV}(P_{q,k},U_H)=O_\ell(q^{-1/2})
   \]
   uniformly in \(k\) and \(p\).

Thus, along any sequence of fields on which \(r\ge2\) is fixed, \(k<r\) gives distance tending to one, \(k=r\) has limit inferior at least \(1-1/r!\), and a single additional nonzero coefficient suffices for joint convergence to uniformity. In the large-characteristic setting the boundary limit is exactly \(1-1/\ell!\). If \(r=1\), weight one already gives distance \(1/q\). If \(r<\ell\), comparison to uniform on the **full** \(\mathbb F_q^\ell\) instead of \(H\) always has distance at least \(1-q^{r-\ell}\). These are statements for the specified full-order model; they do not presume an infinite sequence of primes with \(d\) a power of two.

## 2. Support and the boundary calculation

The \(\pm g^j\), \(0\le j<d\), list all nonzero field elements once, in antipodal pairs. The random coefficient vector thus corresponds bijectively to a uniform size-\(k\) set \(S\subseteq\mathbb F_q^\times\) containing at most one element from each pair \(\{u,-u\}\). For each odd \(e\), its coordinate is
\[
 C(g^e)=\sum_{u\in S}u^e.
\]
Frobenius gives the relations defining \(H\). There are \(M=2^k\binom{d}{k}\) choices of \(S\), so comparison with a \(q^r\)-point uniform law gives the claimed lower bound by the event consisting of the support.

Suppose \(k\le r\) and \(p>2k-1\). To count the support, let two admissible sets \(S,T\) have the same output, and take the multiset \(W=S\sqcup(-T)\) of size \(2k\). Its odd power sums \(s_i(W)\) through \(2k-1\) vanish. Write \(b_i\) for the elementary symmetric functions of \(W\). For odd \(m\le2k-1\), Newton's relation
\[
 m b_m=\sum_{i=1}^{m}(-1)^{i-1} b_{m-i}s_i(W)
\]
has zero right side inductively: terms with odd \(i\) have \(s_i=0\), and terms with even \(i\) have \(m-i\) odd and smaller. Since \(m\ne0\) in \(\mathbb F_q\), every odd \(b_m\) is zero. The monic degree-\(2k\) polynomial with multiset of roots \(W\) is even; therefore \(W\) has equal multiplicities at \(u\) and at \(-u\). On each antipodal pair this says that the signed indicator of \(S\) equals that of \(T\). The antipodal restriction makes those indicators unique, so \(S=T\). The output law is therefore uniform on exactly \(M\) points, giving the identity.

The asymptotic boundary uses \(M/q^r\to 1/r!\) at \(k=r\). If \(r=1\), the single retained exponent is \(1\), for which \(k=1\) is uniform on \(\mathbb F_q^\times\). The graph comparison follows from \(|H|=q^r\).

## 3. Uniform Fourier estimates without independent supports

It suffices to use the coordinates in \(E\), since projection is a bijection on \(H\). For a nonzero frequency \(a=(a_e)_{e\in E}\), write
\[
 F_a(u)=\sum_{e\in E}a_eu^e,\qquad
 z_j=\Re\psi(F_a(g^j)),\qquad \psi(u)=\exp(2\pi i\,{\rm Tr}_{\mathbb F_q/\mathbb F_p}(u)/p).
\]
The polynomial \(F_a\) is odd and nonconstant, has degree at most \(2\ell-1\), and its degree is prime to \(p\). Conditional on a support the signs are independent, so for the Fourier coefficient of the projected law,
\[
 \widehat P(a)=\binom{d}{k}^{-1}[t^k]\prod_{j=0}^{d-1}(1+z_jt).
 \tag{1}
\]
The conditional-support average in (1) is exact: there is no replacement of the fixed-weight sample by an independent-coefficient model.

The additive-character Weil bound for \(F_a\) and \(2F_a\) gives, uniformly in \(a\ne0\), 
\[
 \left|\sum_j z_j\right|\le \frac{(2\ell-2)\sqrt q+1}{2}\le\ell\sqrt q,\qquad
 \frac1d\sum_j z_j^2\le \frac12+\frac{(2\ell-2)\sqrt q+1}{4d}.
 \tag{2}
\]
For the first inequality, pair \(g^j\) with \(-g^j\) and subtract the character value \(1\) at zero. For the second, use \(z_j^2=(1+\Re\psi(2F_a(g^j)))/2\) and the same pairing. These bounds also apply to degree one (the complete nontrivial linear sum vanishes).

**Low and moderate weight.** Set \(\rho=\sqrt{k/q}<1/\sqrt 2\). The convergent logarithmic series at \(|t|=\rho\) and \(|z_j|\le1\) give
\[
 \log\left|\prod_j(1+z_jt)\right|
 \le \rho\left|\sum_j z_j\right|+\frac{d\rho^2}{2(1-\rho)}
 \le\ell\sqrt{k}+k.
\]
Indeed each tail after the linear term is bounded in absolute value by \(\sum_{i\ge2}\rho^i/i\le\rho^2/[2(1-\rho)]\), and \(d\rho^2<k/2\). Cauchy's coefficient bound in (1) and \(\binom{d}{k}\ge(d/k)^k\) now yield
\[
 |\widehat P(a)|\le e^{\ell\sqrt{k}}\left(3e\sqrt{k/q}\right)^k ,
 \tag{3}
\]
where the \(e\) in the parenthesis is Euler's number. We used \(q/d\le3\).

**High weight.** Use the triangle inequality followed by Maclaurin's inequality for the normalized elementary symmetric polynomial of \((|z_j|)_j\). Then Cauchy–Schwarz and (2) give, for sufficiently large \(q\) depending only on \(\ell\),
\[
 |\widehat P(a)|\le \left(\frac1d\sum_j|z_j|\right)^k
 \le \left(\frac1d\sum_j z_j^2\right)^{k/2}
 \le (3/4)^{k/2}.
 \tag{4}
\]

**Conversion to total variation.** Character orthogonality and Cauchy–Schwarz give
\[
 2d_{\rm TV}(P_{q,k},U_H)\le
 \left(\sum_{a\ne0}|\widehat P(a)|^2\right)^{1/2}
 \le q^{r/2}\max_{a\ne0}|\widehat P(a)|.
 \tag{5}
\]
For fixed \(k>r\), use (3). For uniformity in \(k\), first handle \(k=r+1\) from (3), using that \(r+1\le\ell+1\). Let \(B_\ell=(\ell+1)/\log(4/3)\). For \(k\ge B_\ell\log q\), (4) is at most \(q^{-(\ell+1)/2}\). For \(r+2\le k<B_\ell\log q\), choose \(\epsilon=1/[2(\ell+2)]\). Uniformly in this interval, \(\ell/\sqrt{k}+\log(3e)+\tfrac12\log k\le(\epsilon/2)\log q\) for large enough \(q\), so (3) is at most \(q^{-k(1-\epsilon)/2}\le q^{-(r+1)/2}\). This proves the stated uniform bound. The same calculation on any single coordinate uses only \(q-1\) nontrivial frequencies: for a Frobenius-dependent exponent first pass to its retained ancestor, a bijective change of that single field coordinate. Hence each marginal has distance \(O_{\ell,k}(q^{(1-k)/2})\) for fixed \(k\ge2\). In particular, at weight two and large characteristic the marginals approach uniformity while the joint distance approaches \(1/2\) for \(\ell=2\), and one for \(\ell>2\).

Sharpness here concerns the threshold location and the exact sparse-range law when specified; no matching lower bound on the decay exponent above the threshold is claimed.

## 4. Relation to prior work and scope

- Boudgoust and Lapiha, [Leftover Hash Lemma(s) Over Cyclotomic Rings, full version](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf), §5, Lemma 34 and Appendix A.1, treat a fixed-weight ternary source and bound a well-spreadness quantity through individual residue factors under their cyclotomic hypotheses. Their split one-block case motivates the model here. The object here is direct **joint** variation of selected unseeded residue coordinates, not well-spreadness for an arbitrary factorization or a leftover hash lemma for public random matrices.
- Esgin, Steinfeld and Zhao, [MatRiCT+, §III and Lemma 1](https://eprint.iacr.org/2021/545.pdf), give their preceding partition-and-sample well-spreadness analysis for individual slots. The present result does not analyze that protocol or its parameters.
- Lai, Marino, Robinson and Wan, [Moment Subset Sums over Finite Fields](https://pmc.ncbi.nlm.nih.gov/articles/PMC10941333/), §2 and §4, study a different ordinary-subset moment model and use distinct-coordinate character sums. Biswas et al., [Sharp Endpoint Extension Inequalities for the Moment Curve on Finite Fields](https://arxiv.org/html/2508.08377v1), §2.1, use Newton identities for the ordinary moment curve with consecutive exponents and allow repetitions. The count here instead compares two signed antipodal-free sets using odd moments, and combines that exact sparse boundary with a joint total-variation estimate uniform through the largest weights.
- The square-root estimate in (2) is the classical [Weil additive character bound](https://doi.org/10.1073/pnas.34.5.204), also stated in the form used here in the moment-subset paper's Theorem 4.

The full multiplicative order, degree scaling \(d=(q-1)/2\), and consecutive odd exponents are hypotheses, not generic conclusions about all split cyclotomic quotients or arbitrary coordinate choices. The comparison is strictly about a standalone mathematical distribution with no ciphertexts, secrets, hidden inputs, or extraction algorithm. The accompanying verifier enumerates small synthetic probability spaces and tests identities used by the proof; it is not an empirical substitute for the uniform asymptotic estimates.
