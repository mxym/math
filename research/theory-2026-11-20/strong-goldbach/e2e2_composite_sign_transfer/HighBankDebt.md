# Actual adverse high-bank mass of the repaired determinant score

Use exactly the two repaired scores \(F_{1,J},F_{2,J}\), with their original disjoint bank families and \(d=d_J\), of [the composite-only determinant transfer](Proof.md#4-neutral-banks-that-repair-all-fixed-bounded-ranks-on-both-legs). In a regular macroscopic box, the real admissible \(t\)-length \(\ell_{u,v}\) is \(\gg x^{.5125}\) for all short labels in the box. Use the true unmasked short-prime labels of that box, minus target primes as before, and put \(M=\mathfrak S(N)\mathcal V\) for this box. The constants of macroscopic comparison and the lower bound for the overlap length are fixed. No lower is asserted in arbitrarily thin intersection windows.

For every sufficiently large fixed \(J\), as \(N=x\) tends to infinity through the even targets, the **negative part** of the repaired bracket in (4) has contribution
\[
 \gg d_J^{-2}M
\tag{1}
\]
on explicit genuine opposite-sign composite-composite rows. The lower constant is independent of \(J\); thresholds in \(x\) may depend on \(J\). This neither bounds the net adverse-plus-favorable sum away from zero nor contradicts an \(E_2+E_2\) conjecture.

Write \(K=J+1\), so \(d=.02/(4K^2+4K-1)\), and fix actual distinct unit primes
\[
 a\in(x^{.55d},x^{.56d}],\qquad b\in(x^{.60d},x^{.61d}],
 \qquad r\in(x^{2d},x^{2.1d}].
\]
Choose one actual prime \(r_i\) in each of the \(K\) original leg-1 banks, put \(A=ab\prod_{i=1}^{K}r_i\), and count the physical rows
\[
 t=A T,\qquad s=r Z,\qquad u A T+v r Z=N,\qquad
 P^-(T),P^-(Z)>W=x^{2.1d}.
\tag{2}
\]
The choices of short labels and all named primes are pairwise disjoint in scale (or by the disjoint label windows for \(u,v\)), and all are units to \(N\). Thus the two slopes are coprime.

The only distinct primes \(\le D=x^d\) in \(t\) are \(a,b\), with \(ab>D\). The complete small-divisor sum is \(0\), while \(F_D(t)=-\log(t/(ab))\), so \(F_{1,J}(t)=-B_1(t)\log(t/(ab))\). Both \(t,s\) are composite; for \(s\), \(Z\gg x^{.5125-2.1d}>1\). Since \(s\) has no prime \(\le D\), \(F_{2,J}(s)=\log s>0\). Thus the actual repaired scores \(\lambda-F_{1,J}\) and \(\lambda-F_{2,J}\) have opposite signs. Repeated primes in \(T\) or \(Z\) make no difference to these assertions. The pair \(a,b\) is unique and the \(s\)-label \(r\) is unique since \(Z\) has no prime \(\le W\). The same row can occur for several choices of the \(r_i\); their combined weight is bounded by the **exact** weight \(B_1(t)\): an admissible tuple is one term \(\prod_i H_i^{-1}\) in its product of sums over distinct bank divisors, and for a fixed tuple \(T\) is uniquely determined. Both actual long logs in the resulting lower bound are \(\gg L\).

For each fixed tuple including \(u,v\), solve the last equation in (2) in the common integer parameter \(j\), with \(T=T_0+vrj\), \(Z=Z_0-uAj\). The real parameter interval has length
\[
 Y=\frac{\ell_{u,v}}{v A r}\gg x^{.017}.
\tag{3}
\]
Indeed the \(K\) banks used here have sum of upper exponents \(K(K+3)d\); after adding the exponents for \(a,b,r\),
\[
 Ar\le x^{(K(K+3)+3.27)d}<x^{.008}.
\]
For \(K\ge4\) the last inequality is exactly \(.4(4K^2+4K-1)>K^2+3K+3.27\), checked at \(K=4\) and then increasing.

Apply the dimension-two lower fundamental lemma to the **two true cofactor forms** in this parameter, with cutoff \(W\) and level \(E=x^{.014}\). At a prime \(p\) outside the slopes the two roots are distinct unless \(p\mid N\); if \(p\) divides either slope, one form is a nonzero constant by the target-unit assumptions and the other has exactly one root. At \(2\) the roots agree since \(N\) is even and all slope factors odd. Thus there is no local obstruction. The dimension upper-product axiom has absolute constants: compare to two roots for \(p\ge3\), whose inverse product on \(z_1\le p\le z_2\) is at most \((\log z_2/\log z_1)^2(1+O(1/\log z_1))\) by Mertens and the convergent \(p^{-2}\) corrections, with the lone prime \(2\) absorbed in the absolute constant. The [bounded lower weights of Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206) apply uniformly; the level-to-cutoff ratio \(\log E/\log W=.014/(2.1d)\) tends to infinity as \(J\to\infty\), so the main lower factor exceeds \(1/2\) for all sufficiently large fixed \(J\). Open squarefree CRT moduli \(m\le E\): their errors are \(O(2^{\omega(m)})\) per modulus and sum to \(O(x^{.014}L)\), negligible relative to the displayed main by (3). The Euler product of allowed residue fractions is at least the standard Goldbach product truncated at \(W\) times \(\prod_{p\le W}(1-1/p)^2\), since at primes in the slopes one root instead of two can only increase the product. The full singular-series comparison is uniform for fixed \(J\), using \(\sum_{p\mid N,p>W}1/p\le L/(W\log W)\). Hence the count of **actual** cofactor pairs in (2) is
\[
 \gg \frac{Y\,\mathfrak S(N)}{d^2 L^2}
\tag{4}
\]
with a lower constant independent of \(J\) for sufficiently large fixed \(J\).

Multiply (4) by \((\log u)(\log v)L^2\prod_i H_i^{-1}\) times an absolute positive constant. Each of the \(a,b,r\) reciprocal-prime sums is bounded below by a fixed positive constant by Mertens at the two endpoints (omitting target primes costs \(o_J(1)\)). Each normalized bank reciprocal sum is exactly \(1\), including its target exclusions. Summing \(Y=\ell_{u,v}/(v A r)\) now gives (1) with the exact same \(\mathcal V\). This argument is a direct count in each physical progression, with no distribution hypothesis for the long cofactor terms.

For scale comparison, apply the analogous dimension-two **upper** bound to actual prime \(t,s\) in the original untagged progression of length \(\ell_{u,v}/v\gg x^{.025}\). One may sieve at \(x^{.001}\) with level \(x^{.01}\). The same root count has no slope factors below the cutoff, so \(R\ll M\) on this regular box. In (4) the error is \(o_J(M)\) since \(M\asymp x\mathfrak S(N)\). Consequently a positive part at least of the order in (1) is compulsory for this particular calibrated score. The proof rules out treating its whole negative tail as an absolute \(o_J(1)M\) error after first taking the large-target limit; it does not rule out a signed compensation estimate. The earlier [bounded-rank removal for the reflected midpoint](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8) uses another score and is not subject to this particular witness.
