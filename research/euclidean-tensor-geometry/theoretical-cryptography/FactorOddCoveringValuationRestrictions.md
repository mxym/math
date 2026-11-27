# New valuation restrictions on odd distinct covering systems

Research note, 27 November 2026. Let \(\mathcal C\) be a finite covering of \(\mathbb Z\) by one congruence class per distinct odd modulus \(m>1\), and let \(Q=\operatorname{lcm}_{m\in\mathcal C}m\).

**Theorem.** Its least common multiple has the following properties.

1. If \(7\nmid Q\), then \(v_3(Q)\ge3\), \(v_5(Q)\ge2\), and \(v_3(Q)\ge4\) or \(v_5(Q)\ge3\). Equivalently, using the known \(45\mid Q\), at least one of \(315,2025,3375\) divides \(Q\).
2. If \(v_3(Q)=2\) and \(v_5(Q)=1\), then \(7\cdot11\cdot13\mid Q\), so \(45045\mid Q\).

The result strengthens the divisibility conclusion \(45\mid Q\) in [Dai, Li, Li and Yi, *On the moduli of distinct covering systems*, arXiv:2611.15110v1](https://arxiv.org/abs/2611.15110). It does not show that \(7\mid Q\) unconditionally, improve their global minimum-modulus bound, or settle the existence of an odd distinct covering system. The proof keeps upper bounds on the small-prime exponents and conditions on the complements of the **two** pure-prime-power towers. It uses the distortion and scalar convex comparison of that paper, with the details needed here given below.

## 1. A distortion bound with capped small-prime exponents

We rule out each profile in the table below. Fix \(b_3,b_5\in\mathbb N\cup\{\infty\}\) and a missing prime \(r\ge7\), assuming \(v_i(Q)\le b_i\) for \(i=3,5\) and \(r\nmid Q\). Put
\[
 s_i=\sum_{1\le e\le b_i}i^{-e},\qquad g_i=(1-s_i)^{-1}\quad(i=3,5).
\]
Under the Chinese remainder decomposition modulo \(Q\), delete from the \(i\)-coordinate all classes with pure-power modulus \(i^e\) in the given family. Such a class has uniform measure \(i^{-e}\), and there is at most one for each \(e\), so the surviving coordinate has uniform measure at least \(1-s_i>0\). The conditional uniform law on the surviving \(i\)-coordinate assigns any residue modulo \(i^e\) probability at most \(g_i i^{-e}\). The \(3\)- and \(5\)-coordinate events are independent before conditioning, so we can take the product of the two conditional laws. The remaining classes must cover the surviving product.

We first bound the probability \(L_5\) covered by all remaining classes whose largest prime factor is \(5\). Such a modulus is \(3^j5^e\), with \(j,e\ge1\), \(j\le b_3\) and \(e\le b_5\). Use the union bound and the two conditional residue bounds to obtain
\[
 L_5\le g_5s_5\sum_{j=1}^{b_3}g_3 3^{-j}
     =g_5s_5(\mathbb E D_3-1),
\]
where for \(i=3,5\), \(D_i=1+T_i\) and
\[
 \mathbb P(T_i\ge e)=g_i i^{-e}\quad(1\le e\le b_i),\qquad
 \mathbb P(T_i\ge e)=0\quad(e>b_i).
\]
The pure-prime-power classes have already been excluded; in particular there is no \(j=0\) in this stage. We do not distort the \(5\)-coordinate.

At each later prime \(p\mid Q\), in increasing order, extend the current measure uniformly in the \(p\)-coordinate. Given the preceding coordinates \(x\), write \(\alpha_p(x)\) for the uniformly covered fraction of its \(p\)-fibre from classes whose largest prime factor is \(p\). For a chosen \(\delta_p\in[0,1/2]\), set \(c_p=(1-\delta_p)^{-1}\). Assign that covered part of the fibre total probability \(c_p(\alpha_p(x)-\delta_p)_+\), uniform on that part, and assign the rest to the uncovered part, also uniform there. Parts of size zero need no assignment. Both densities relative to uniform are at most \(c_p\): when \(\alpha_p(x)>\delta_p\) the uncovered density is \(c_p\), and otherwise it is \(1/(1-\alpha_p(x))\le c_p\). The covered density is also at most \(c_p\).

This preserves all preceding marginal laws. In particular the total probability assigned to the \(p\)-stage classes under the final measure is
\[
 L_p=c_p\,\mathbb E(\alpha_p(x)-\delta_p)_+.
\]
In this distorted joint law, each preceding coordinate \(q\) has, conditionally on its predecessors, probability at most \(\gamma_q q^{-e}\) in a specified \(q^e\)-class, where \(\gamma_q=g_q\) for \(q=3,5\) and \(\gamma_q=c_q\) otherwise.

Here is the convex comparison used to estimate \(L_p\). For one coordinate, replace the indicators of residue classes with exponents \(e_l\) by the nested indicators \(\boldsymbol{1}_{T\ge e_l}\), where the tail probabilities for \(T\) are the specified bounds (zero beyond the allowed cap). These indicators give an upper bound on \(\mathbb E\phi(\sum_l a_l I_l)\) for every increasing convex \(\phi\) and nonnegative weights \(a_l\). Indeed order the classes by increasing exponent, set \(A_l=\sum_{i\le l}a_i\), and telescope \(\phi\) over the original indicators. The \(l\)-th increment is at most \(I_l(\phi(A_l)-\phi(A_{l-1}))\) by convexity, whereas all these inequalities become equalities for the nested indicators. Apply this replacement from the latest preceding coordinate backwards, conditioning on the actual coordinates earlier than the current one and the independent, already replaced coordinates later than it. The conditional residue bounds suffice for every replacement. This is the scalar convex comparison in Dai–Li–Li–Yi, Theorem 2.6, here with capped exponents where relevant.

On a \(p\)-fibre, use the union bound over moduli \(mp^e\), with \(m\) supported on the preceding primes. Distinctness permits at most one such class for each \((m,e)\), with conditional uniform fibre weight \(p^{-e}\) if its congruence modulo \(m\) is satisfied. After the above comparison, that congruence is replaced by \(m\mid \prod_{q<p}q^{T_q}\). Summing over divisors and over \(e\ge1\) now gives
\[
 L_p\le \frac{c_p}{p-1}\mathbb E \big(X_p-\delta_p(p-1)\big)_+,
 \qquad X_p=\prod_{\substack{q<p\\q\in\{3,5\}\text{ or }q\ge7,\ q\ne r}}D_q .
 \tag{1}
\]
For ordinary \(q\ge7\), the independent variables are defined by \(D_q=1+T_q\) and \(\mathbb P(T_q\ge e)=c_qq^{-e}\) for \(e\ge1\). Adding these factors for absent primes (other than \(r\)) enlarges \(X_p\) and the bound, so it suffices to include every possible \(q\) in the product and to sum the resulting bounds over all \(p\ge7\), \(p\ne r\). If the sum of those upper bounds and the bound on \(L_5\) is less than one, there is positive final probability of an uncovered point, contradicting the supposed covering.

## 2. Finite computation and the infinite tail

For each ordinary \(p\le30\,000\), use \(\delta_p=3/10\), except for the exceptions in the code: in case D use \(33/100\) at primes \(p<61\); in case E use \(1/3\) at \(p=13,19\) and \(1/4\) at \(p=17\). For \(p>30\,000\), use \(\delta_p=1/2\).

For the finite range, put \(a=\delta_p(p-1)\) and \(Z_p=\prod_{q<p}\min(D_q,10)\), with the same prime range as in \(X_p\). From \(Z_p\le X_p\),
\[
 \mathbb E(X_p-a)_+=\mathbb E X_p-a+\mathbb E(a-X_p)_+
 \le \mathbb E X_p-a+\sum_{t<a}(a-t)\mathbb P(Z_p=t).
 \tag{2}
\]
All \(a\le9900\) in this range. The probabilities of \(Z_p=t\) for \(t\le9900\) are updated by multiplicative convolution, retaining only entries at most \(9900\). This is valid because all factors are positive integers. Their only possible prime divisors are \(2,3,5,7\), because the factors are at most ten. The distribution of \(\min(D_q,10)\) is obtained by differences of the defining tails up to the last point, which receives all remaining probability. Use a scale \(W=10^{30}\) and round every probability contribution upward. Keep the full first and third moments separately, multiplying and rounding them upward too. For the noncapped law,
\[
 \mathbb E D_q=1+\frac{\gamma_q}{q-1},\qquad
 \mathbb E D_q^3=1+\frac{\gamma_q(7q^2-2q+1)}{(q-1)^3};
\]
for finite caps use \(1+\sum_{e=1}^{b_q}((e+1)^j-e^j)\gamma_q q^{-e}\) for each moment \(j=1,3\). Formula (2) uses only positive coefficients on the rounded probabilities and moments and subtracts the exact \(a\).

For \(p>30\,000\), use
\[
 (x-a)_+\le\frac{4x^3}{27a^2}\quad(x\ge0,a>0),
 \qquad L_p\le\frac{32\,\mathbb E X_p^3}{27(p-1)^3}.
\]
The first inequality follows from \(4x^3-27a^2x+27a^3=(2x-3a)^2(x+3a)\) when \(x\ge a\), with the other range immediate. The moment update and this bound are evaluated prime by prime through \(10^6\).

Here is the infinite-tail calculation (Dai–Li–Li–Yi, Lemma 2.10, specialized to the constants in use). Write \(J=\pi(10^6)=78498\), \(b=J-1\), and \(M\) for the upper bound on the third moment after \(p_J\). The third-moment multiplier at any \(p>10^6\) is at most \(1+15/(p-1)\), since \(2(7p^2-2p+1)\le15(p-1)^2\) for \(p\ge27\). Rosser's inequality \(p_j>j\log j\) gives \(p_j-1>(j-1)\log(j-1)\) by applying it to \(p_{j-1}\). Using \(1+x\le e^x\) and an integral bound for \(\sum_{k>J}1/((k-1)\log(k-1))\), the moment just before \(p_j\), \(j>J\), is at most \(M(\log(j-1)/\log b)^{15}\). Thus the tail bound is at most
\[
 \frac{32M}{27(\log b)^{15}}\int_b^\infty\frac{(\log x)^{12}}{x^3}\,dx
 \le \frac{32M}{27b^2(\log b)^2(2\log b-12)}
 < \frac{32M}{27\cdot1210\,b^2}.
\]
The integrand is decreasing for \(x\ge b\); the integral inequality follows by substituting \(x=be^u\) and using \((1+u/\log b)^{12}\le e^{12u/\log b}\). Finally \(\log b>11\) via \(e<11/4\) and the exact integer inequality \(11^{11}<b\,4^{11}\).

The [standalone directed-integer verifier](verify_factor_odd_covering_valuation.js) produces the following upward-rounded bounds in parts per million. The finite column includes \(L_5\); the total is rounded separately.

| Case | Missing prime \(r\) | \(b_3\) | \(b_5\) | Finite | Middle | Tail | Total |
|---|---:|---:|---:|---:|---:|---:|---:|
| A | 7 | 2 | \(\infty\) | 864685 | 4884 | 321 | 869888 |
| B | 7 | \(\infty\) | 1 | 893491 | 5188 | 341 | 899018 |
| C | 11 | 2 | 1 | 902353 | 4398 | 289 | 907038 |
| D | 13 | 2 | 1 | 972914 | 5853 | 384 | 979150 |
| E | 7 | 3 | 2 | 986112 | 5799 | 381 | 992291 |

All totals are less than \(10^6\). Cases A and B force \(v_3(Q)\ge3\) and \(v_5(Q)\ge2\) if \(7\nmid Q\), and E excludes the residual pair \((3,2)\). In the \((2,1)\) case, A, C and D respectively force \(7,11,13\mid Q\). This completes the proof. The computer part is solely the finite directed-integer calculation; the residue classes are arbitrary, and the proof is not a Lean formalization.
