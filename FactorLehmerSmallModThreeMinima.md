# Exact degree-eight and degree-ten minima in the uniform mod-three reciprocal class

Let $P$ be monic reciprocal of even degree $D$, with integer coefficients, constant coefficient 1, all inner coefficients $2\bmod3$, and no root of unity. The [previous auxiliary resultant](FactorLehmerAuxiliaryModThree.md) gives a degree-uniform gap, establishes the exact degree-four minimum $\rho=1.722083805\ldots$, and leaves even degrees $8$ through $52$ not divisible by 3 as the only possible improvements on that quartic. We obtain:

* In degree 8 the **unique** minimizer is
\[
 P_8=x^8-x^7-x^6+2x^5-x^4+2x^3-x^2-x+1,\quad
                   2.2773<M(P_8)<2.2774 .
\]
Every other polynomial in the class has $M>2.3$.
* In degree 10 the **unique** minimizer is
\[
 P_{10}=x^{10}-x^9-x^8-\cdots-x+1,\quad
                    1.9970<M(P_{10})<1.9971 .
\]
Every other polynomial in the class has $M>2$.
* In degree 14, $M>17221/10000$. Hence any improvement on the quartic would have even degree $16\le D\le52$ not divisible by 3.

The congruence class is the $r=2,m=3$ case of [Jha–Thangadurai, Theorem 1.2](https://arxiv.org/abs/2610.33631). This concerns arbitrary integer coefficients in the indicated residue class, not just small height, Salem numbers, or unrestricted Lehmer. It is a self-contained exhaustive check for the stated thresholds and does not assume completeness of a small-measure database, such as [Mossinghoff's compilation](https://github.com/mossinghoff/Mahler-Measure-Database).

## 1. The moment sieve

Fix a rational threshold $R>1$, put $D=2m$, and suppose $M(P)\le R$. With reciprocals grouped into $m$ pairs, let $r_i\ge1$ denote the outer radius in each pair, so $\prod r_i=M(P)$. In particular every root has modulus at most $R$, and it is in fact strictly smaller: a root $\alpha$ and its complex conjugate are algebraic units, so $\alpha\bar\alpha=R^2$ would be a rational algebraic unit greater than 1. The same strict disk contains every derivative root by Gauss–Lucas.

Write $s_k=\sum_\alpha\alpha^k$. The reciprocal pairing gives
\[
 |s_k|\le\sum_{i=1}^m(r_i^k+r_i^{-k})
 \le 2(m-1)+R^k+R^{-k}.
\tag{1}
\]
The second inequality follows by putting $u_i=k\log r_i\ge0$ and successively using $\cosh u+\cosh v\le1+\cosh(u+v)$. This uses the bound on the **product** of all outer radii, not a separate house bound for every root.

Let $a_0=1,a_1,\ldots,a_m$ be the leading half of the coefficient list, the rest being forced by reciprocity. At step $k\le m$, Newton's identities give
\[
 s_k=-k a_k-\sum_{j=1}^{k-1}a_j s_{k-j}.
\]
Thus (1) bounds the next residue-2 integer $a_k$ in an exact finite interval depending only on the current prefix. Enumerating this interval gives a complete finite enumeration; there is no imputed bound on coefficient height.

The code also prunes each prefix using two necessary disk tests. Put $P(x)=x^m Q(x+x^{-1})$. The leading $k+1$ coefficients of the monic trace polynomial $Q$ are known from those of $P$ by expanding the binomials; the change is triangular. Its roots have modulus at most $R+R^{-1}$, so we take a rational $T$ strictly greater than this. The known leading $k+1$ coefficients of $P$ and $Q$ determine the whole derivative polynomials of degrees $k$, up to irrelevant common factors. By Gauss–Lucas the roots of those derivatives are strictly within $R$ and $T$. These derivative disk tests apply without any assumption of real trace roots.

For the integer disk test, divide the variable by the given radius by scaling coefficients to an integral multiple of $F(Rz)$ or $F(Tz)$. If the positive leading coefficient is $A$ and the constant is $B$, all roots strictly inside the unit disk imply $|B|<A$. On the unit circle $|z^dF(1/z)|=|F(z)|$ for real coefficients, so Rouché shows that
\[
          \bigl(A F(z)-B z^dF(1/z)\bigr)/z
\]
again has all roots strictly inside. Recursing gives necessary strict inequalities at every degree. The checker uses this exact integer procedure and can divide each coefficient list by its positive common divisor. After a full prefix, it applies (1) through $k=4D$ and the exact disk test to the whole reciprocal polynomial.

## 2. Two exact terminal exclusions

First remove polynomials having any cyclotomic factor. If $\Phi_j$ divides a degree-$D$ polynomial, its degree $\varphi(j)\le D$ and $j\le2D^2$, using $\varphi(j)\ge\sqrt{j/2}$ from the prime-power formula. Each $\Phi_j$ is generated from the monic factors of $x^j-1$, and integer long division determines divisibility. This test includes repeated cyclotomic factors.

For the other candidates, let $\alpha_1,\ldots,\alpha_D$ be the roots, counted with multiplicities. A product of any $m$ roots has modulus at most $M(P)$, and the maximal such modulus equals $M(P)$: take the larger member of every reciprocal pair. Consequently $M(P)\le R$ requires
\[
 \big|e_m(\alpha_1^k,\ldots,\alpha_D^k)\big|
             \le \binom Dm R^k,\qquad k\ge1.
\tag{2}
\]
The left side is the absolute trace of the $k$-th power of the middle exterior compound of the companion matrix. It is computed without building that matrix: first calculate the integer power sums $s_{jk}$ of $P$, then use Newton's identities up through $e_m$ on the rooted powers. Test $k=1,\ldots,48$, using exact integer comparisons after clearing the rational denominator of $R^k$. It is enough to find one violation. No root precision is assumed in either exclusion.

The exhaustive replay gives:
\[
\begin{array}{c|c|r|r|r|r|l}
D&R&\text{completed prefixes}&\text{terminal tests survive}&
       \text{cyclotomic}&\text{violates (2)}&\text{not excluded}\\\hline
8&23/10&220&118&50&67&P_8\\
10&2&797&236&81&154&P_{10}\\
14&17221/10000&7963&991&303&688&\text{none}
\end{array}
\]
Here the terminal survivor column is after the $4D$ power sums and strict whole-polynomial disk test. The largest required $k$ in (2) is respectively $47,26,23$. The complete verification uses only the standard library and integer or rational arithmetic.

## 3. Isolate the minimizing witnesses

Both displayed witnesses satisfy the coefficient congruence and the exact cyclotomic exclusion. It remains to certify that they attain values below their enumeration thresholds.

For $P_{10}$ the trace polynomial is $t^5-t^4-6t^3+3t^2+7t-1$. It has opposite endpoint signs on the five disjoint intervals
\[
 (-2,-9/5),\quad(-6/5,-1),\quad(0,1/5),\quad(6/5,3/2),
 \quad(12/5,5/2).
\]
These account for all five roots. The first four yield unit-circle root pairs of $P_{10}$, while the last yields a positive real reciprocal pair with outer member less than 2. The signs of $P_{10}$ at $1.9970,1.9971$ isolate that member, which is its measure.

For $P_8$, use disks of radius $10^{-6}$ around the following Gaussian rational centers:
\[
 -1.43789337,\qquad 1.09354797\pm0.62287067\,i.
\]
At each center, write the exact Taylor coefficients as $b_j$. The checker verifies $r\max(|\Re b_1|,|\Im b_1|)>\sum_{j\ne1}r^j(|\Re b_j|+|\Im b_j|)$, where $r=10^{-6}$. By Rouché each disk contains exactly one root. Their moduli are bounded by strict rational intervals $(1.437892,1.437895)$ and $(1.258496,1.258499)$ for the real and complex centers respectively, via squared rational radius comparisons. All are outside the unit circle. Their inverses give three inside roots. The remaining two are on the unit circle: the trace polynomial $t^4-t^3-5t^2+5t+3$ changes sign between $-1/2$ and $-2/5$. Thus the product of the three certified outer moduli gives the displayed interval for $M(P_8)$, strictly below $23/10$.

The surviving non-cyclotomic polynomial in each of degrees 8 and 10 therefore is the unique minimizer there.

**Replay.** `python3 -O verify_factor_lehmer_small_mod_three.py` tests all three degrees. Give explicit degree arguments to run just the selected cases. The finite enumeration does not depend on the approximate decimal root centers being exact roots; their strict Rouché bounds are checked in rational arithmetic.
