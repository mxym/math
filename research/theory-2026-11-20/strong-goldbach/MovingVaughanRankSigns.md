# Moving Vaughan cuts eliminate negative rank-three terms

For the same actual \(K_P\)-weighted matched carrier considered in [AsymmetricVaughanSmoothResidual.md](AsymmetricVaughanSmoothResidual.md), a different exact Vaughan decomposition uses cutoffs depending on the **whole shifted integer**. It removes the negative three-prime term and proves a sign for all squarefree four-prime integers in that decomposition. These are identities and signs of coefficients, not a bound for their correlation with the shifted-prime discrepancy. The price is losing the earlier square-root smooth support for general ranks. This is not a Goldbach theorem.

## 1. The genuinely moving cut remains Type I

Use \(c_{\rm sf}\), \(J=[x,1.5x)\), \(Q_0=x^q,\ .618<q<.625\), and the maximal divisor-weighted Type I estimate (1) from the asymmetric note. For each **fixed integer** \(m\in J\), set
\[
              U(m)=H(m)=m/Q_0,\qquad V(m)=Q_0^2/m .
\]
These positive thresholds satisfy \(U(m)V(m)=Q_0\), and \(H(m)>V(m)\) for large \(x\) since \(q<2/3\). Apply the exact Vaughan identity at each \(m\) with that pair of parameters. Its \(\Lambda_{\le V(m)}\) term vanishes. In the \(\mu_{\le U(m)}*\log\) term, once the divisor \(d\) is fixed, its additional test is just the moving prefix condition \(m\ge dQ_0\). In \(\mu_{\le U(m)}*\Lambda_{\le V(m)}*1\), collect \(r=d l\le Q_0\) and use \(dQ_0\le m\le Q_0^2/l\). All such cuts are intervals in the free variable, and the usual prime log/divisor coefficients and partial summation fit the available Type I reserve. Thus only \(d>H(m)\), \(l>V(m)\), \(m=d l h\), remains.

Repeat the two subtractions (3) and (4) of the largest-prime descent at this \(Q_0\), including the cross term:

* In \(a(d;l h)\Lambda(l)\), write \(d=c z\) and fix \(c,l,h\) with \(r=c l h\le Q_0\). With \(m=r z\), the condition \(d>H(m)\) is just \(l h<Q_0\), independent of \(z\); \(l>V(m)\) imposes the lower interval \(z>Q_0^2/(l r)\).
* In \(\mu(d)a'(l;d,h)\), set \(l=e z'\), \(r=e d h\le Q_0\) and \(m=r z'\). The exact conditions are \(z'<dQ_0/r\) and \((z')^2>Q_0^2/(er)\), both ordinary interval endpoints for the free \(z'\). Continue to use \(\log z'\) by partial summation.
* In the cross term use \(d=c z\), \(l=e z'\), and fix \(c,z,e,h\) with \(r=e h c z\le Q_0\). The same free interval cuts hold and the additional \(c e h z'\le Q_0\) is an upper endpoint. Fixed divisor coefficients cost at most \(\tau_5(r)\) as before.

Thus the moving cuts cause **no** unknown weighted progression sums. Summing \(l\mid k\) uses the exact divisor identity (7) with the now fixed value \(V(m)\) for each \(m\). On squarefree \(m\) the result is the same formula
\[
 \sum_m c_{\rm sf}(m)\Lambda(m)
   =\sum_{m\in J}c_{\rm sf}(m)\mathcal B_{\rm mov}(m)+O_B(xL^{-B}),
\tag{1}
\]
where
\[
\begin{split}
 \mathcal B_{\rm mov}(m)&=\sum_{\substack{dk=m\\d>H,\ k>V}}
       b(d;k)\left(1_{k<H}\log k-\sum_{p\mid k,\ p\le V}\log p\right),\\
 b(d;k)&=\mu(d)+\sum_{c\mid d,\ ck\le Q_0}\mu_2(c).
\end{split}
\tag{2}
\]
Here and below \(H,V\) mean the functions of this \(m\). Unlike the earlier square-root support, this keeps \(k<Q_0\). The original coefficient is zero on all prime and semiprime \(m\): a prime \(d>H\) has \(k<Q_0\), and its short sum has only \(c=1\), so \(b=0\). A composite \(d\) cannot occur with \(k>V>1\) if \(m\) has at most two prime factors.

For scale comparison, all \(P^+(m)>Q_0/3\) can still be removed exactly on the odd support. For a prime \(P>Q_0/3\) dividing \(m\), \(P>H\) and \(P>Q_0/k\), so \(b=0\) whenever \(P\mid d\) by the same divisor argument as before. Otherwise \(d\mid t=m/P<3H\); proper divisors of odd \(t\) are at most \(t/3<H\), so only \(d=t\) occurs. Then \(k=P>H,V\) and its bracket is zero. This is only a cutoff at exponent \(q\), **not** at exponent \(1/2\).

## 2. Exact three-prime result and nonpositive four-prime result

Call a prime factor *large* in this paragraph if it is \(\ge H\). In rank three only \(d\) a pair, \(k\) a prime in \((V,H)\), can contribute, by the preceding prime-\(d\) observation. With \(j\) large primes, its coefficient is \(2(1-j)\log k\) as in [the triple sieve note](WeightedTripleMarkedSieve.md). If \(j\ge2\), the prospective prime \(k\) is at most \(m/H^2=V\), so it is excluded. If \(j=1\) the coefficient is zero. If \(j=0\), each prime exceeds \(m/H^2=V\) since the other two are \(<H\), and all three complements contribute. Thus on the full actual rank-three support
\[
  \mathcal B_{\rm mov}(p_1p_2p_3)=
   \begin{cases}2\log m&\max_i p_i<H(m),\\0&\max_i p_i\ge H(m).\end{cases}
\tag{3}
\]
This removes rather than bounds the **negative** rank-three chamber in this alternate representation; the earlier positive wedge and its unresolved outer part are unchanged.

For four distinct primes, \(\mathcal B_{\rm mov}(m)\le0\) pointwise. The exact check is:

1. A nonzero \(d\)-triple can only have complementary prime \(k=p\in(V,H)\), with bracket \(\log p\). Its coefficient is
\[
  b(d;k)=-2\,\#\{\text{pairs within }d\text{ whose product is }\ge H\}
                      +4\,\#\{\text{prime factors of }d\ge H\}.
\]
This is just the expansion of the short sum by complement inside \(d\), and the \(c=1\) term cancels \(\mu(d)=-1\). If \(d\) has at most one large factor the displayed coefficient is nonpositive: one large factor produces at least two such pairs. Two large factors are impossible since then \(k\le m/H^2=V\).
2. For \(d\) a pair and \(k\ge H\), the bracket is nonpositive. The pair has coefficient \(2(1-\#\{\text{large factors in }d\})\ge0\), as two large factors again force \(k\le V\). Such terms are nonpositive.
3. The only possible positive terms have \(d\) a pair with no large prime, \(V<k<H\), and a marked prime \(p\mid k,\ p>V\). It is unique because \(V^2>H\) for all large \(x\) (\(5q>3\)). Write \(k=p t\), then \(t\le V\). The positive part is \(2\log p\). Charge this to the \(d'=d t\) triple with complement \(p\), where the prime factors of \(d'\) are all \(<H\) and \(d>H\) was an eligible pair. For each fixed \(p\), the potentially charged positive terms correspond injectively to these eligible pairs inside \(d'\), by the omitted factor \(t\). The triple coefficient in item 1 supplies exactly \(-2\log p\) for each pair of product \(\ge H\), so it absorbs all the charges. Its own \(d'>H\) and \(p>V\) tests are automatic. This leaves no positive rank-four terms.

All weak/strict boundaries agree with the original short sum and the stated activation \(k>V,d>H\). As \(W\ge0\), rank four therefore contributes at most the corresponding **nonnegative reference charge** \(\sum_{\Omega(m)=4}(-\mathcal B_{\rm mov}(m))R_N(m)\) to the actual upper bound, not zero or a negative discrepancy. No bound making this whole charge negligible is asserted.

At rank five, both signs still occur on stable actual prime exponent chambers. For an example with no subset equality throughout \(H(m)=x^{(.375,.382)+o(1)}\), use center exponents \((.284,.048,.167,.137,.364)\) giving \(4(\log p_1-\log p_2+\log p_5)>0\). The centers \((.260,.227,.214,.199,.100)\) give \(-12\log p_5\). These follow by summing (2) over the proper subsets \(D\); for a direct integer check, use exponent units of \(1/1000\), exclude subsets with \(D\)-sum \(\le h\) or complement sum \(\le1000-2h\), and for each allowed \(D\) compute
\[
 b_D=2(-1)^{|D|}-\!\!\sum_{C\subseteq D,\ \sum(D\setminus C)<h}(-2)^{|C|}.
\]
The resulting respective per-prime integer coefficient vectors are \((4,-4,0,0,4)\) and \((0,0,0,0,-12)\); none of the proper subset exponent sums changes its threshold comparison for \(375\le h\le382\). Positive-width neighboring boxes with distinct actual primes preserve these signs. Higher-rank mixed coefficients therefore cannot be dropped.

## 3. Original Goldbach scope

The \(n\)-side \(W\) is always composite, containing many independent marked prime factors. Even an exact shifted-prime asymptotic for \(W(N-m)\) would not itself give an \(n,m\) prime pair. The earlier centered-marker inference instead requires the actual **complete** low signed bound
\[
 \sum_{\substack{n\in I\\y\le P^-(n)<x^{.155}}}(a(n)-b(n))K_P(n)
       \le .010 M_N
\]
(with the high and presieve reserves of the centered/polynomial notes). \(W\) contributes only one positive composite subcarrier of it, and its own prime-reference unit is a narrowing-dependent constant times \(M_N/\varepsilon\), not \(M_N\). Among the uncovered sets are true two-prime \(n=s q\) with \(\log_x s\in(.10,.14)\): they have the strictly positive eligible-free \(K_{P_3}=\lambda(2\lambda-1)^2\), \(\lambda=\log q/\log n\), and do not meet any of the flexible carrier's many required prime labels. Their one-sided actual reflected-prime discrepancy, and others of the uncaptured low carrier, still need independent control.

No unproved signed estimate or full binary Goldbach conclusion follows from (1)–(3).

For comparison, [Arneth (September 2026)](https://zenodo.org/records/23016346) analyzes balanced five-factor coefficients of another signed sieve selector, and [the October candidate architecture](https://zenodo.org/records/23504447) uses other exact Vaughan and divisor-interval identities. The signs here are those of the literal adaptive coefficient (2) with its stated moving cuts, not a uniform parity-sign statement for arbitrary coefficient schemes.
